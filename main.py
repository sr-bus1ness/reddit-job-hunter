"""
BOT JOB VIDEO EDITOR
====================
Monitora subreddits em busca de vagas de edição de vídeo e envia ao Telegram.

Fontes de dados (modo REDDIT_SOURCE=auto, o padrão):
  1. RSS do Reddit  -> UMA requisição com todos os subreddits juntos (r/a+b+c).
                       ATENÇÃO: o Reddit anunciou o fim do RSS em 13/11/2026.
  2. Arctic Shift   -> arquivo público e gratuito do Reddit (sem chave de API).
                       Usado automaticamente quando o RSS falha ou deixa de existir.

Variáveis de ambiente:
  TELEGRAM_TOKEN, TELEGRAM_CHAT_ID   obrigatórias (exceto em DRY_RUN=1)
  REDDIT_SOURCE   auto | rss | arctic   (padrão: auto)
  DRY_RUN=1       não envia nada ao Telegram e não grava o histórico
  DEBUG=1         mostra por que cada post foi aceito/rejeitado
  REDDIT_USER_AGENT   opcional, ex.: "github-actions:video-job-bot:v2 (by /u/seu_usuario)"
"""
from __future__ import annotations

import html
import json
import os
import re
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from urllib.parse import urlparse
from zoneinfo import ZoneInfo

import requests

# ============================================================================
# CONFIGURAÇÃO
# ============================================================================
SUBREDDITS = [
    "B2BForHire",
    "CreatorServices",
    "Filmmakers",
    "FindVideoEditors",
    "HireAnEditor",
    "VideoEditing",
    "VideoEditingJobs",
    "VideoEditingRequests",
    "VideoEditor_forhire",
    "VideoEditors",
    "VideoEditors_forhire",
    "YouTubeEditorForHire",
    "YouTubeEditorsForHire",
    "forhire",
]

# Subreddits onde a maioria dos posts é de editores se OFERECENDO: exigimos
# sinal de contratação no TÍTULO (ou tag [HIRING]).
STRICT_SUBS = {
    "b2bforhire",
    "creatorservices",
    "forhire",
    "videoeditor_forhire",
    "videoeditors_forhire",
    "youtubeeditorforhire",
    "youtubeeditorsforhire",
}

# Subreddits dedicados a vagas/pedidos: contratação é implícita.
JOB_BOARD_SUBS = {
    "findvideoeditors",
    "hireaneditor",
    "videoeditingjobs",
    "videoeditingrequests",
}

SEEN_FILE = os.environ.get("SEEN_FILE", "seen_posts.json")
SOURCE_MODE = os.environ.get("REDDIT_SOURCE", "auto").strip().lower()
DRY_RUN = os.environ.get("DRY_RUN") == "1"
DEBUG = os.environ.get("DEBUG") == "1"

WINDOW = timedelta(hours=24)            # só posts publicados nas últimas 24 h
SEEN_RETENTION = timedelta(days=7)      # por quanto tempo lembrar posts enviados
CLOCK_SKEW = timedelta(minutes=10)      # tolerância para relógios dessincronizados
ALERT_AFTER = timedelta(hours=3)        # avisa no Telegram se tudo falhar por este tempo
ALERT_EVERY = timedelta(hours=12)       # intervalo mínimo entre avisos

RSS_LIMIT = 100
RSS_CHUNK = 5                           # tamanho dos grupos no fallback do RSS
RSS_ASSUMED_COVERAGE = timedelta(hours=6)
ARCTIC_URL = "https://arctic-shift.photon-reddit.com/api/posts/search"

MAX_WAIT = 70                           # espera máxima (s) por rate limit
RUN_BUDGET = 6 * 60                     # orçamento total da execução (s)
TELEGRAM_PAUSE = 1.1                    # pausa entre mensagens (s)

USER_AGENT = os.environ.get(
    "REDDIT_USER_AGENT",
    "github-actions:video-editor-job-bot:v2.0 (personal job alert bot)",
)

_START = time.monotonic()
_SESSION = requests.Session()
_SESSION.headers.update({"User-Agent": USER_AGENT})
_host_ready_at: dict[str, float] = {}


def log(*args):
    print(*args, flush=True)


def debug(*args):
    if DEBUG:
        print(*args, flush=True)


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def time_left() -> float:
    return RUN_BUDGET - (time.monotonic() - _START)


# ============================================================================
# MODELOS E UTILITÁRIOS DE TEXTO
# ============================================================================
@dataclass
class Post:
    id: str
    title: str
    text: str
    url: str
    subreddit: str
    created: datetime
    source: str = "rss"
    removed: bool = False


@dataclass
class Decision:
    accepted: bool
    reason: str


class TextExtractor(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self._skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip += 1

    def handle_endtag(self, tag):
        if tag in ("script", "style") and self._skip:
            self._skip -= 1

    def handle_data(self, data):
        if not self._skip:
            self.parts.append(data)

    def get_text(self):
        return " ".join(self.parts)


_FOOTER_RE = re.compile(
    r"\s*submitted by\s+/?u/\S+\s*(?:\[link\]\s*)?(?:\[comments\]\s*)?$", re.I
)


def clean_html(value: str) -> str:
    parser = TextExtractor()
    parser.feed(value or "")
    text = re.sub(r"\s+", " ", parser.get_text()).strip()
    return _FOOTER_RE.sub("", text).strip()


def fold(text: str) -> str:
    """minúsculas, sem acentos, aspas normalizadas e espaços colapsados."""
    text = (text or "").replace("\u2019", "'").replace("\u2018", "'")
    text = unicodedata.normalize("NFKD", text)
    text = "".join(c for c in text if not unicodedata.combining(c))
    return re.sub(r"\s+", " ", text.lower()).strip()


_URL_RE = re.compile(r"https?://\S+|www\.\S+")


def fold_body(text: str) -> str:
    return fold(_URL_RE.sub(" ", text or ""))


def parse_date(value):
    if not value:
        return None
    try:
        date = parsedate_to_datetime(value)
    except Exception:
        try:
            date = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        except Exception:
            return None
    if date is None:
        return None
    if date.tzinfo is None:
        date = date.replace(tzinfo=timezone.utc)
    return date.astimezone(timezone.utc)


def normalize_id(raw: str) -> str:
    """'t3_abc123' (RSS) e 'abc123' (Arctic Shift) viram a mesma chave."""
    raw = (raw or "").strip()
    if raw.startswith("t3_"):
        raw = raw[3:]
    return raw


# ============================================================================
# FILTRO DE VAGAS
# ============================================================================
def _rx(*patterns: str) -> re.Pattern:
    return re.compile("|".join(f"(?:{p})" for p in patterns))


# --- tags no título: [HIRING], [FOR HIRE] ... --------------------------------
_TAG_RE = re.compile(r"[\[\(\{]\s*([a-z][a-z /_-]{1,24}?)\s*[\]\)\}]")
HIRING_TAGS = {"hiring", "task", "paid", "job", "gig", "paid gig", "vaga", "contratando"}
SEEKER_TAGS = {"for hire", "forhire", "available", "offer", "offering", "freelancer",
               "portfolio", "available for hire", "seeking work"}
DISCUSSION_TAGS = {"discussion", "meta", "question", "help", "feedback", "showcase",
                   "promo", "advice", "rant", "review"}

# --- quem está se oferecendo (não é vaga) -------------------------------------
SEEKER_TITLE_RE = _rx(r"\bfor hire\b", r"\bhire me\b", r"\bavailable for\b", r"\bsou (?:um |uma )?editor")
SEEKER_ANY_RE = _rx(
    r"\bhire me\b",
    r"\bavailable for (?:work|hire|projects?|freelance|commissions?|new clients?)\b",
    r"\bi(?:'m| am|m) (?:a|an) (?:(?!looking|need|seeking|hiring)\w+ ){0,3}editors?\b",
    r"\bmy (?:portfolio|rates?|services|reel|showreel|prices?|pricing)\b",
    r"\bdm me for (?:my )?(?:rates?|portfolio|samples?|pricing|work)\b",
    r"\bi (?:offer|provide|specializ\w+|specialis\w+)\b",
    r"\bi (?:will|can) (?:edit|cut|make|create|deliver)\b",
    r"\bopen for (?:commissions?|work|projects?|bookings?)\b",
    r"\b(?:commissions?|slots?|spots?) (?:are )?open\b",
    r"\btaking (?:on )?(?:new )?(?:clients?|projects?|commissions?)\b",
    r"\bnow booking\b",
    r"\baccepting (?:new )?(?:clients?|projects?|commissions?)\b",
    r"\blooking for (?:more )?(?:clients?|work|gigs?|projects?|jobs?|freelance|opportunit\w+|commissions?)\b",
    r"\bseeking (?:work|clients?|projects?|opportunit\w+|employment)\b",
    r"\bmeu portfolio\b", r"\bdisponivel para\b", r"\bofereco\b",
)

# --- vagas que não interessam --------------------------------------------------
EXCLUDE_ANY_RE = _rx(
    r"(?<!not )(?<!non-)(?<!non )(?<!no )\bunpaid\b",
    r"\bfree work\b", r"\bwork for free\b", r"\bfor exposure\b",
    r"\bno pay\b", r"\bwithout pay\b", r"\bsem remuneracao\b",
    r"\b(?:rev(?:enue)?|profit)[- ]?share only\b",
)
EXCLUDE_TITLE_RE = _rx(r"\bcourses?\b", r"\btutorials?\b", r"\bmasterclass\b",
                       r"\bgiveaway\b", r"\bvolunteers?\b", r"\bvoluntari[oa]s?\b")
# perguntas/discussões (ignoradas quando há tag [HIRING])
DISCUSSION_TITLE_RE = _rx(
    r"\bhow (?:do|to|can|should|would)\b",
    r"\bany(?:one)? (?:know|recommend|have|else)\b",
    r"\b(?:advice|tips|feedback|critique|review my|rate my|thoughts on)\b",
    r"\bwhat(?:'s| is| are| should)\b",
    r"\b(?:which|what) (?:software|laptop|pc|computer|gpu|camera|app|plugin)\b",
    r"\bshowcase\b", r"\bi (?:made|edited|created)\b",
    r"\bmy (?:first|latest|new) (?:video|edit|reel|film)\b",
)

# --- intenção de contratar -------------------------------------------------------
HIRING_RE = _rx(
    r"\bhiring\b",
    r"\bwe(?:'re| are) (?:looking|searching|hiring|recruiting|seeking|in need)\b",
    r"\b(?:looking|searching|in search|on the hunt) for\b",
    r"\blooking to hire\b",
    r"\b(?:need|needs|needed)\b",
    r"\bseeking\b", r"\bwanted\b", r"\bto hire\b", r"\brecruiting\b",
    r"\bpaid (?:gig|job|position|role|work|editing|project|opportunity|test)\b",
    r"\b(?:job|gig|position|opening|vacancy|opportunity)\b",
    r"\bbudget\b", r"\bapply\b",
    r"\bsend (?:me |us )?(?:your |a |some )?(?:portfolio|samples?|reel|examples?|work|cv|resume|rates?)\b",
    r"\b(?:busco|buscamos|se busca|buscando|contratando|contratamos|contrata-se|procuro|"
    r"procuramos|preciso|precisamos|necesito|necesitamos|vaga|vagas)\b",
)

# --- cargo: edição de vídeo ------------------------------------------------------
_VIDEO_WORDS = (r"video|film|footage|reels?|shorts?|short[- ]?form|long[- ]?form|tiktok|youtube|yt|"
                r"podcast|clip|clips|gaming|anime|documentary|vlog|vod")
VIDEO_ROLE_RES = [
    re.compile(rf"\b(?:{_VIDEO_WORDS})\s*(?:and \w+ )?edit(?:or|ors|ing)\b"),
    re.compile(r"\bedit(?:ing)?\s+(?:\w+\s+){0,2}?(?:videos?|footage|clips?|shorts|reels?|podcasts?|vlogs?)\b"),
    re.compile(r"\b(?:premiere(?: pro)?|after effects|davinci(?: resolve)?|final cut(?: pro)?|capcut)\b"),
    re.compile(r"\bmotion (?:designers?|graphics?|graphic designers?)\b"),
    re.compile(r"\bpost[- ]?production\b"),
    re.compile(r"\bcolou?rists?\b"),
    re.compile(r"\bclippers?\b"),
    re.compile(r"\b(?:editor(?:es|a|as)? de video|edicao de video|edicion de video|"
               r"editores de video|videomaker|videografo)\b"),
]
_BARE_EDITOR_RE = re.compile(r"\b(?:(\w+) )?editors?\b(?! ?-? ?in[- ]chief)")
_NON_VIDEO_EDITOR_PREFIX = {
    "copy", "text", "code", "photo", "image", "picture", "managing", "news", "book",
    "script", "story", "html", "markdown", "level", "map", "audio", "sound", "wiki",
    "feature", "features", "chief", "online", "rich", "visual",
}
_VIDEO_SUB_KEYS = ("video", "editor")
_BARE_EDIT_RE = re.compile(r"\bedit(?:ing|or|ors|s)?\b")

# --- outros cargos (vaga de vendas, dev, etc. que só cita "vídeo") ---------------
OTHER_ROLES_RE = _rx(
    r"\bsales\b", r"\bsalesperson\b", r"\bclosers?\b", r"\bsetters?\b", r"\bsdrs?\b", r"\bbdrs?\b",
    r"\blead gen\w*", r"\bcold (?:call\w*|email\w*|dm\w*|outreach)\b", r"\btelemarket\w*",
    r"\bappointment\b", r"\baffiliates?\b", r"\brecruiters?\b",
    r"\b(?:web |software |app |full[- ]?stack |front[- ]?end |back[- ]?end )?(?:developers?|programmers?|engineers?|coders?)\b",
    r"\b(?:copy)?writers?\b", r"\bghost ?writers?\b", r"\bscript ?writers?\b",
    r"\bbookkeepers?\b", r"\baccountants?\b",
    r"\b(?:virtual|executive|personal|administrative) assistants?\b", r"\bvas?\b",
    r"\bcustomer (?:support|service|success)\b", r"\bsupport agents?\b",
    r"\bcommunity managers?\b", r"\bsocial media managers?\b", r"\bmoderators?\b",
    r"\btranslators?\b", r"\btranscri\w+\b", r"\bvoice ?(?:over|actors?)\b", r"\bnarrators?\b",
    r"\bmusicians?\b", r"\bcomposers?\b", r"\bphotograph\w*\b", r"\bdesigners?\b",
    r"\bseo\b", r"\bmedia buyers?\b", r"\bvendedor\w*\b", r"\bdesenvolvedor\w*\b",
)


def title_tags(title: str) -> set[str]:
    return {t.strip() for t in _TAG_RE.findall(title)}


def find_video_role(text: str, subreddit: str = "") -> int | None:
    """Posição da primeira menção a um cargo de edição de vídeo, ou None."""
    positions: list[int] = []
    for rx in VIDEO_ROLE_RES:
        m = rx.search(text)
        if m:
            positions.append(m.start())
    for m in _BARE_EDITOR_RE.finditer(text):
        if (m.group(1) or "") not in _NON_VIDEO_EDITOR_PREFIX:
            positions.append(m.start())
            break
    if not positions and any(k in subreddit.lower() for k in _VIDEO_SUB_KEYS):
        m = _BARE_EDIT_RE.search(text)
        if m:
            positions.append(m.start())
    return min(positions) if positions else None


def classify(post: Post) -> Decision:
    """Decide se um post é uma vaga de edição de vídeo. Devolve também o motivo."""
    title = fold(post.title)
    body = fold_body(post.text)
    sub = post.subreddit.lower()
    body_head = body[:600]

    def no(reason: str) -> Decision:
        return Decision(False, reason)

    if post.removed or body in ("[removed]", "[deleted]"):
        return no("post removido/deletado")

    tags = title_tags(title)
    if tags & SEEKER_TAGS:
        return no(f"tag de quem se oferece: {sorted(tags & SEEKER_TAGS)}")
    if tags & DISCUSSION_TAGS:
        return no(f"tag de discussão: {sorted(tags & DISCUSSION_TAGS)}")
    has_tag = bool(tags & HIRING_TAGS)

    # 1) quem está se oferecendo
    if not has_tag:
        m = SEEKER_TITLE_RE.search(title) or SEEKER_ANY_RE.search(f"{title} {body[:400]}")
        if m:
            return no(f"parece oferta de serviço: '{m.group(0)}'")

    # 2) exclusões (não pago, curso, tutorial, perguntas)
    m = EXCLUDE_ANY_RE.search(f"{title} {body}")
    if m:
        return no(f"exclusão: '{m.group(0)}'")
    m = EXCLUDE_TITLE_RE.search(title)
    if m:
        return no(f"exclusão no título: '{m.group(0)}'")
    if not has_tag:
        m = DISCUSSION_TITLE_RE.search(title)
        if m:
            return no(f"pergunta/discussão: '{m.group(0)}'")

    # 3) o cargo precisa ser edição de vídeo
    if find_video_role(title, sub) is not None:
        role = "cargo no título"
    else:
        other = OTHER_ROLES_RE.search(title)
        if other:
            return no(f"título indica outro cargo: '{other.group(0)}'")
        pos = find_video_role(body_head, sub)
        if pos is None:
            return no("nenhum cargo de edição de vídeo no título/início do texto")
        other = OTHER_ROLES_RE.search(body_head)
        if other and other.start() < pos:
            return no(f"texto cita outro cargo antes: '{other.group(0)}'")
        role = "cargo no texto"

    # 4) precisa ser contratação
    title_intent = has_tag or bool(HIRING_RE.search(title))
    body_intent = bool(HIRING_RE.search(body_head))
    if sub in STRICT_SUBS:
        if not title_intent:
            return no("sub de ofertas: sem sinal de contratação no título")
    elif not (title_intent or body_intent or sub in JOB_BOARD_SUBS):
        return no("sem sinal de contratação")

    return Decision(True, f"{role}; contratação "
                          f"{'tag' if has_tag else 'título' if title_intent else 'texto/sub'}")


# ============================================================================
# NICHO
# ============================================================================
NICHES = [
    ("Shorts / Reels / TikTok", [r"shorts?", r"reels?", r"tiktoks?", r"short[- ]?form", r"vertical"]),
    ("YouTube / Long-form", [r"youtube", r"\byt\b", r"long[- ]?form", r"vlogs?"]),
    ("Gaming", [r"gaming", r"gamers?", r"minecraft", r"roblox", r"gameplay", r"fortnite", r"valorant"]),
    ("Streaming / Clips", [r"twitch", r"\bkick\b", r"stream(?:er|ing|s)?", r"\bvods?\b", r"clipp\w+", r"highlights?"]),
    ("Documentário", [r"documentar(?:y|ies|io)", r"docuseries"]),
    ("Podcast", [r"podcasts?"]),
    ("Motion Design", [r"motion (?:design|graphics?)", r"after effects", r"animation"]),
    ("Publicidade / Marketing", [r"\bads?\b", r"advertis\w+", r"marketing", r"commercials?", r"\bugc\b", r"promo\w*"]),
    ("Anime / Recap", [r"anime", r"naruto", r"recaps?", r"manga"]),
    ("Educacional", [r"online course", r"courses?", r"educational", r"e-?learning", r"lessons?"]),
    ("Eventos / Casamento", [r"wedding", r"events?", r"real estate"]),
    ("Corporativo", [r"corporate", r"\bb2b\b", r"explainer", r"webinars?", r"training videos?"]),
]
_NICHE_RES = [(name, re.compile(r"\b(?:" + "|".join(words) + r")\b")) for name, words in NICHES]


def get_niche(title: str, body: str = "") -> str:
    """Pontua cada nicho (título vale 3x o texto). Empate vai para a ordem da lista."""
    t, b = fold(title), fold_body(body)
    best_name, best_score = "Não identificado", 0
    for name, rx in _NICHE_RES:
        score = 3 * len(rx.findall(t)) + len(rx.findall(b[:1500]))
        if score > best_score:
            best_name, best_score = name, score
    return best_name


# ============================================================================
# REMUNERAÇÃO
# ============================================================================
_NUM = r"\d{1,3}(?:[.,]\d{3})+(?:[.,]\d{1,2})?|\d+(?:[.,]\d{1,2})?"
_MAG = r"(?:[kmb]\b|mm\b|bn\b|\s?(?:thousand|million|billion|mil|milhao|milhoes|milh[aã]o|milh[oõ]es)\b)"
_CUR_PREFIX = r"US\$|CA\$|A\$|R\$|\$|€|£|(?<![a-z])(?:usd|eur|gbp|brl|cad|aud)(?![a-z])"
_CUR_SUFFIX = r"\$|€|£|usd|eur|gbp|brl|reais|dollars?|euros?|pounds?|bucks"

_MONEY_PREFIX_RE = re.compile(
    rf"(?P<cur>{_CUR_PREFIX})\s?(?P<n1>{_NUM})(?P<m1>{_MAG})?"
    rf"(?:\s*(?:-|–|—|to|até)\s*(?:{_CUR_PREFIX})?\s?(?P<n2>{_NUM})(?P<m2>{_MAG})?)?",
    re.I,
)
_MONEY_SUFFIX_RE = re.compile(
    rf"(?<![\w$€£.,])(?P<n1>{_NUM})(?P<m1>{_MAG})?"
    rf"(?:\s*(?:-|–|—|to)\s*(?P<n2>{_NUM})(?P<m2>{_MAG})?)?\s?(?P<cur>{_CUR_SUFFIX})(?![a-z])",
    re.I,
)

_CUR_LABEL = {
    "us$": "US$", "$": "US$", "usd": "US$", "dollar": "US$", "dollars": "US$", "bucks": "US$",
    "r$": "R$", "brl": "R$", "reais": "R$",
    "€": "€", "eur": "€", "euro": "€", "euros": "€",
    "£": "£", "gbp": "£", "pound": "£", "pounds": "£",
    "ca$": "CA$", "cad": "CA$", "a$": "A$", "aud": "A$",
}
_MAG_VALUE = {"k": 1e3, "thousand": 1e3, "mil": 1e3,
              "m": 1e6, "mm": 1e6, "million": 1e6, "milhao": 1e6, "milhoes": 1e6,
              "milhão": 1e6, "milhões": 1e6,
              "b": 1e9, "bn": 1e9, "billion": 1e9}

_UNIT_PREFIXED_RE = re.compile(
    r"^\s*(?:/|\bper\b|\ba\b|\ban\b|\beach\b|\bp/|\bfor each\b|\bpor\b)\s*"
    r"(?:finished |final |edited |every |one |single |raw |short |full )?"
    r"(?P<u>hours?|hrs?|h|videos?|vid|minutes?|mins?|months?|mo|weeks?|wk|days?|years?|yr|annum|"
    r"shorts?|reels?|clips?|projects?|edits?|episodes?|ep|thumbnails?|hora|horas|minuto|minutos|"
    r"mes|mês|semana|dia|projeto|vídeo|video)\b",
    re.I,
)
_UNIT_ADJ_RE = re.compile(r"^\s*(?P<u>hourly|monthly|weekly|daily|yearly|annually|flat)\b", re.I)
_UNIT_MAP = {
    "hour": "hora", "hr": "hora", "h": "hora", "hourly": "hora", "hora": "hora",
    "video": "vídeo", "vid": "vídeo", "short": "vídeo", "reel": "vídeo", "clip": "vídeo",
    "edit": "vídeo", "episode": "vídeo", "ep": "vídeo", "thumbnail": "vídeo", "vídeo": "vídeo",
    "minute": "minuto", "min": "minuto", "minuto": "minuto",
    "month": "mês", "mo": "mês", "monthly": "mês", "mes": "mês", "mês": "mês",
    "week": "semana", "wk": "semana", "weekly": "semana", "semana": "semana",
    "day": "dia", "daily": "dia", "dia": "dia",
    "year": "ano", "yr": "ano", "annum": "ano", "yearly": "ano", "annually": "ano",
    "project": "projeto", "projeto": "projeto", "flat": "projeto",
}

_PAY_STRONG_RE = re.compile(
    r"\b(?:pay|pays|paying|paid|payment|budget|rates?|compensation|salary|wage|fees?|offer|"
    r"offering|earn|earning|pricing|price|bonus|flat|starting (?:at|from)|"
    r"pago|paga|pagamos|pagando|valor|orcamento|orçamento|salario|salário|cache|cachê)\b"
    r"|\$/?hr", re.I)
_PAY_WEAK_RE = re.compile(r"\b(?:from|up to|around|about|approx\w*|give|gives|get|at|ate|até)\b", re.I)
_REVENUE_AFTER_RE = re.compile(
    r"^\W{0,3}(?:(?:in|of|per \w+ in|a \w+ in|/\w+ in)\s+)?(?:total\s+|annual\s+|monthly\s+|ad\s+)?"
    r"(?:revenues?|sales|profits?|arr|mrr|ad spend|funding|valuation|turnover|ebitda|"
    r"faturamento|receita|vendas|followers|subscribers|subs|views|seguidores|inscritos|visualizacoes)\b",
    re.I)
_REVENUE_BEFORE_RE = re.compile(
    r"\b(?:revenues?|made|making|generat\w+|grossed?|grossing|raised|valued|valuation|worth|doing|"
    r"hit|hitting|reached|reaching|grew|growing|scaled|exit(?:ed)?|sold for|turnover|"
    r"faturamento|faturou|faturando|receita|arrecad\w+)\b[^.!?\n]{0,25}$", re.I)
_NEGOTIABLE_RE = re.compile(
    r"\b(?:negotiable|negociavel|negociável|depends on experience|to be discussed|a combinar|open to offers)\b",
    re.I)


def parse_number(s: str) -> float:
    """Entende '1,500', '1.500', '15.50', '15,50' e '1.234,56'."""
    s = s.strip()
    if "," in s and "." in s:
        dec = "," if s.rfind(",") > s.rfind(".") else "."
        thou = "." if dec == "," else ","
        s = s.replace(thou, "").replace(dec, ".")
    elif "," in s or "." in s:
        sep = "," if "," in s else "."
        parts = s.split(sep)
        if len(parts) > 2 or (len(parts[1]) == 3 and 1 <= len(parts[0]) <= 3):
            s = "".join(parts)          # separador de milhar
        else:
            s = ".".join(parts)         # separador decimal
    return float(s)


def _fmt_amount(value: float) -> str:
    text = f"{int(value):,}" if float(value).is_integer() else f"{value:,.2f}"
    return text.replace(",", "§").replace(".", ",").replace("§", ".")


def _magnitude(token: str | None) -> float | None:
    if not token:
        return None
    return _MAG_VALUE.get(token.strip().lower())


def _money_candidates(text: str):
    """Gera (span, moeda, baixo, alto) para cada valor monetário encontrado."""
    taken: list[tuple[int, int]] = []
    for rx in (_MONEY_PREFIX_RE, _MONEY_SUFFIX_RE):
        for m in rx.finditer(text):
            if any(m.start() < e and m.end() > s for s, e in taken):
                continue
            taken.append((m.start(), m.end()))
            m1, m2 = _magnitude(m.group("m1")), _magnitude(m.group("m2"))
            try:
                low, high = parse_number(m.group("n1")), None
                if m.group("n2"):
                    high = parse_number(m.group("n2"))
            except ValueError:
                continue
            if m1 is None and m2 is not None and high is not None and low < high:
                m1 = m2                       # "$2-3k" = 2k a 3k
            low *= m1 or 1
            if high is not None:
                high *= m2 or 1
            yield m.span(), _CUR_LABEL.get(m.group("cur").lower(), m.group("cur")), low, high, (m1 or m2 or 1)


def get_value(text: str) -> str:
    """Extrai a remuneração oferecida, ignorando faturamento, seguidores etc."""
    text = re.sub(r"\s+", " ", text or "")
    best = None  # (score, ordem, texto)
    for order, ((start, end), cur, low, high, mag) in enumerate(_money_candidates(text)):
        top = high if high is not None else low
        # "US$ 20 milhões", "$2M ARR": nunca é pagamento de um editor
        if mag >= 1e6 or top >= 100_000:
            continue
        left = text[max(0, start - 60):start]
        right = text[end:end + 60]
        if _REVENUE_AFTER_RE.search(right) or _REVENUE_BEFORE_RE.search(left):
            continue
        unit = None
        um = _UNIT_PREFIXED_RE.match(right) or _UNIT_ADJ_RE.match(right)
        if um:
            raw_unit = um.group("u").lower()
            unit = _UNIT_MAP.get(raw_unit) or _UNIT_MAP.get(raw_unit.rstrip("s"))
        score = (2 if _PAY_STRONG_RE.search(left[-35:]) else 0) \
            + (1 if _PAY_WEAK_RE.search(left[-12:]) else 0) \
            + (2 if unit else 0)
        # valores altos sem nenhum contexto de pagamento são suspeitos
        if score < 2 and top > 2000:
            continue
        if best is None or score > best[0]:
            if high is not None and high != low:
                amount = f"{cur} {_fmt_amount(low)}–{_fmt_amount(high)}"
            else:
                amount = f"{cur} {_fmt_amount(low)}"
            if unit == "projeto":
                amount += " (projeto)"
            elif unit:
                amount += f"/{unit}"
            best = (score, order, amount)
    if best:
        return best[2]
    if _NEGOTIABLE_RE.search(text):
        return "A combinar"
    return "Não informado"


# ============================================================================
# REDE
# ============================================================================
class FetchError(Exception):
    def __init__(self, message: str, status: int | None = None):
        super().__init__(message)
        self.status = status


def _reset_seconds(resp: requests.Response):
    for header in ("Retry-After", "X-RateLimit-Reset"):
        value = resp.headers.get(header)
        if value:
            try:
                return float(value)
            except ValueError:
                pass
    return None


def http_get(url: str, *, params: dict | None = None, retries: int = 2) -> requests.Response:
    """GET com respeito a rate limit (429/Retry-After/X-RateLimit-*) e orçamento de tempo."""
    host = urlparse(url).netloc
    last: FetchError | None = None
    for attempt in range(retries + 1):
        wait = _host_ready_at.get(host, 0) - time.monotonic()
        if wait > 0:
            if wait > MAX_WAIT or wait > time_left():
                raise FetchError("rate limit: espera longa demais", 429)
            time.sleep(wait)
        if time_left() <= 0:
            raise FetchError("orçamento de tempo da execução esgotado")
        try:
            resp = _SESSION.get(url, params=params, timeout=(10, 30))
        except requests.RequestException as exc:
            last = FetchError(f"erro de rede ({type(exc).__name__})")
            time.sleep(min(2 ** attempt, 5))
            continue

        if resp.status_code == 200:
            remaining = resp.headers.get("X-Ratelimit-Remaining")
            reset = _reset_seconds(resp)
            try:
                if remaining is not None and float(remaining) < 1 and reset:
                    _host_ready_at[host] = time.monotonic() + reset + 1
            except ValueError:
                pass
            return resp

        if resp.status_code in (429, 500, 502, 503, 504):
            wait = (_reset_seconds(resp) or 5 * (attempt + 1)) + 1
            last = FetchError(f"HTTP {resp.status_code}", resp.status_code)
            if wait > MAX_WAIT or wait > time_left():
                break
            time.sleep(wait)
            continue

        raise FetchError(f"HTTP {resp.status_code}", resp.status_code)
    raise last or FetchError("falha desconhecida")


# ============================================================================
# FONTES: RSS DO REDDIT
# ============================================================================
_ATOM = {"a": "http://www.w3.org/2005/Atom"}
_COMMENT_ID_RE = re.compile(r"/comments/([a-z0-9]+)/")


def parse_rss(content: bytes) -> list[Post]:
    try:
        root = ET.fromstring(content)
    except ET.ParseError as exc:
        raise FetchError(f"resposta não é XML válido ({exc})", 200)
    if not root.tag.endswith("feed"):
        raise FetchError("resposta não é um feed Atom", 200)

    posts: list[Post] = []
    for entry in root.findall("a:entry", _ATOM):
        link = entry.find("a:link", _ATOM)
        url = link.attrib.get("href", "") if link is not None else ""
        pid = normalize_id(entry.findtext("a:id", "", _ATOM))
        if not pid:
            m = _COMMENT_ID_RE.search(url)
            pid = m.group(1) if m else url
        published = entry.findtext("a:published", "", _ATOM) or entry.findtext("a:updated", "", _ATOM)
        created = parse_date(published)
        if not pid or not url or created is None:
            continue
        category = entry.find("a:category", _ATOM)
        sub = ""
        if category is not None:
            sub = category.attrib.get("term") or category.attrib.get("label", "").removeprefix("r/")
        if not sub:
            m = re.search(r"/r/([^/]+)/", url)
            sub = m.group(1) if m else ""
        content_html = entry.findtext("a:content", "", _ATOM) or entry.findtext("a:summary", "", _ATOM)
        posts.append(Post(
            id=pid,
            title=html.unescape(entry.findtext("a:title", "", _ATOM) or "").strip(),
            text=clean_html(content_html),
            url=url,
            subreddit=sub,
            created=created,
            source="rss",
        ))
    return posts


def fetch_rss(subs: list[str]) -> list[Post]:
    """Uma única requisição para vários subreddits (r/a+b+c)."""
    url = f"https://www.reddit.com/r/{'+'.join(subs)}/new/.rss"
    resp = http_get(url, params={"limit": RSS_LIMIT})
    return parse_rss(resp.content)


# ============================================================================
# FONTES: ARCTIC SHIFT (arquivo público do Reddit)
# ============================================================================
def post_from_arctic(item: dict) -> Post | None:
    pid = normalize_id(str(item.get("id") or ""))
    created = None
    try:
        created = datetime.fromtimestamp(int(float(item.get("created_utc"))), timezone.utc)
    except (TypeError, ValueError, OverflowError):
        pass
    if not pid or created is None:
        return None
    permalink = item.get("permalink") or f"/comments/{pid}/"
    url = f"https://www.reddit.com{permalink}" if permalink.startswith("/") else permalink
    selftext = item.get("selftext") or ""
    removed = bool(item.get("removed_by_category")) or selftext.strip() in ("[removed]", "[deleted]")
    return Post(
        id=pid,
        title=html.unescape(item.get("title") or "").strip(),
        text=selftext,
        url=url,
        subreddit=item.get("subreddit") or "",
        created=created,
        source="arctic",
        removed=removed,
    )


def fetch_arctic(sub: str, since: datetime) -> list[Post]:
    resp = http_get(ARCTIC_URL, params={
        "subreddit": sub,
        "after": since.strftime("%Y-%m-%d"),   # o filtro fino por hora é feito localmente
        "limit": 100,
        "sort": "desc",
    })
    try:
        data = resp.json()
    except ValueError:
        raise FetchError("Arctic Shift não devolveu JSON", 200)
    if isinstance(data, dict) and data.get("error"):
        raise FetchError(f"Arctic Shift: {str(data['error'])[:80]}", 200)
    items = data.get("data") if isinstance(data, dict) else data
    return [p for p in (post_from_arctic(i) for i in (items or [])) if p]


# ============================================================================
# COLETA (RSS -> fallback Arctic Shift)
# ============================================================================
def collect_posts(now: datetime, mode: str = SOURCE_MODE):
    """Devolve (posts_por_id, fontes_ok, erros)."""
    posts: dict[str, Post] = {}
    errors: list[str] = []
    ok = 0
    since = now - WINDOW
    pending: list[str] = []

    def add(batch: list[Post]):
        for p in batch:
            posts.setdefault(p.id, p)

    if mode in ("auto", "rss"):
        try:
            batch = fetch_rss(SUBREDDITS)
            add(batch)
            ok += 1
            log(f"RSS: {len(batch)} posts em 1 requisição.")
            # O feed traz só os 100 mais novos. Se ele não alcança além das últimas
            # horas, pode haver posts não vistos -> complementa com o arquivo.
            oldest = min((p.created for p in batch), default=None)
            if len(batch) >= RSS_LIMIT and oldest and oldest > now - RSS_ASSUMED_COVERAGE:
                log("RSS possivelmente truncado; complementando com Arctic Shift.")
                pending = list(SUBREDDITS)
        except FetchError as exc:
            errors.append(f"RSS (todos): {exc}")
            log(f"RSS (todos) falhou: {exc}")
            if exc.status == 403:           # bloqueio de IP: dividir não adianta
                pending = list(SUBREDDITS)
            else:
                for i in range(0, len(SUBREDDITS), RSS_CHUNK):
                    chunk = SUBREDDITS[i:i + RSS_CHUNK]
                    try:
                        batch = fetch_rss(chunk)
                        add(batch)
                        ok += 1
                        log(f"RSS grupo {chunk}: {len(batch)} posts.")
                    except FetchError as sub_exc:
                        errors.append(f"RSS {chunk}: {sub_exc}")
                        log(f"RSS grupo {chunk} falhou: {sub_exc}")
                        pending.extend(chunk)
        if mode == "rss":
            pending = []
    else:
        pending = list(SUBREDDITS)

    if pending and mode in ("auto", "arctic"):
        for sub in pending:
            try:
                batch = fetch_arctic(sub, since)
                add(batch)
                ok += 1
                debug(f"Arctic Shift r/{sub}: {len(batch)} posts.")
            except FetchError as exc:
                errors.append(f"Arctic r/{sub}: {exc}")
                log(f"Arctic Shift r/{sub} falhou: {exc}")
            time.sleep(1)
    return posts, ok, errors


# ============================================================================
# HISTÓRICO E ESTADO
# ============================================================================
def load_state() -> tuple[dict, dict]:
    """Lê seen_posts.json. Aceita o formato antigo ({id: data}) e o novo."""
    try:
        with open(SEEN_FILE, "r", encoding="utf-8") as fh:
            raw = json.load(fh)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}, {}
    if not isinstance(raw, dict):
        return {}, {}
    if isinstance(raw.get("posts"), dict):
        seen_raw, meta = raw["posts"], raw.get("meta") or {}
    else:
        seen_raw, meta = raw, {}
    seen = {normalize_id(k): v for k, v in seen_raw.items() if isinstance(v, str)}
    return seen, meta if isinstance(meta, dict) else {}


def save_state(seen: dict, meta: dict) -> None:
    with open(SEEN_FILE, "w", encoding="utf-8") as fh:
        json.dump({"meta": meta, "posts": seen}, fh, indent=2, sort_keys=True)


def prune_seen(seen: dict, now: datetime) -> dict:
    limit = now - SEEN_RETENTION
    kept = {}
    for pid, sent_at in seen.items():
        when = parse_date(sent_at)
        if when and when >= limit:
            kept[pid] = sent_at
    return kept


# ============================================================================
# TELEGRAM
# ============================================================================
def send_telegram(message: str) -> None:
    token = os.environ.get("TELEGRAM_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat_id:
        raise RuntimeError("TELEGRAM_TOKEN/TELEGRAM_CHAT_ID não configurados.")
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    for attempt in range(3):
        try:
            resp = requests.post(url, data={
                "chat_id": chat_id,
                "text": message,
                "disable_web_page_preview": True,
            }, timeout=20)
        except requests.RequestException as exc:
            # não repassa a exceção original: a URL contém o token
            raise RuntimeError(f"falha de rede no Telegram ({type(exc).__name__})") from None
        if resp.status_code == 429:
            try:
                retry = int(resp.json().get("parameters", {}).get("retry_after", 5))
            except (ValueError, AttributeError):
                retry = 5
            time.sleep(min(retry + 1, 30))
            continue
        if resp.status_code != 200:
            raise RuntimeError(f"Telegram respondeu HTTP {resp.status_code}")
        if not resp.json().get("ok"):
            raise RuntimeError("Telegram não confirmou o envio.")
        return
    raise RuntimeError("Telegram: limite de envio excedido após 3 tentativas.")


def build_message(post: Post) -> str:
    title = re.sub(r"\s+", " ", post.title).strip()
    if len(title) > 250:
        title = title[:247] + "..."
    full_text = f"{post.title} {post.text}"
    local_date = post.created.astimezone(ZoneInfo("America/Sao_Paulo")).strftime("%d/%m/%Y às %H:%M")
    return (
        "🤖 BOT JOB VIDEO EDITOR\n\n"
        f"📌 VAGA: {title}\n"
        f"💰 VALOR: {get_value(full_text)}\n"
        f"🎬 NICHO: {get_niche(post.title, post.text)}\n"
        f"📂 SUBREDDIT: r/{post.subreddit}\n"
        f"🕒 PUBLICADA: {local_date}\n\n"
        f"🔗 {post.url}"
    )


# ============================================================================
# PRINCIPAL
# ============================================================================
def update_health(meta: dict, ok: int, errors: list[str], now: datetime) -> None:
    """Avisa no Telegram se TODAS as fontes falharem por muito tempo."""
    if ok > 0:
        meta.pop("failing_since", None)
        return
    failing_since = parse_date(meta.get("failing_since")) or now
    meta["failing_since"] = failing_since.isoformat()
    last_alert = parse_date(meta.get("last_alert"))
    if now - failing_since >= ALERT_AFTER and (not last_alert or now - last_alert >= ALERT_EVERY):
        if DRY_RUN:
            return
        try:
            send_telegram(
                "⚠️ BOT JOB VIDEO EDITOR: sem acesso ao Reddit desde "
                f"{failing_since.astimezone(ZoneInfo('America/Sao_Paulo')):%d/%m %H:%M} "
                "(RSS e Arctic Shift falharam).\n"
                f"Último erro: {errors[-1] if errors else 'desconhecido'}"
            )
            meta["last_alert"] = now.isoformat()
        except Exception as exc:
            log(f"Não consegui enviar o aviso de falha: {exc}")


def main() -> int:
    if not DRY_RUN and not (os.environ.get("TELEGRAM_TOKEN") and os.environ.get("TELEGRAM_CHAT_ID")):
        log("Erro: defina TELEGRAM_TOKEN e TELEGRAM_CHAT_ID (ou use DRY_RUN=1).")
        return 2

    now = utc_now()
    cutoff = now - WINDOW
    seen, meta = load_state()

    posts, ok, errors = collect_posts(now)
    update_health(meta, ok, errors, now)

    fresh = [
        p for p in posts.values()
        if cutoff <= p.created <= now + CLOCK_SKEW and p.id not in seen
    ]
    fresh.sort(key=lambda p: p.created)       # do mais antigo ao mais novo

    sent = 0
    for post in fresh:
        decision = classify(post)
        if not decision.accepted:
            debug(f"[rejeitada] r/{post.subreddit}: {post.title[:80]!r} -> {decision.reason}")
            continue
        message = build_message(post)
        if DRY_RUN:
            log(f"[DRY_RUN] ({decision.reason})\n{message}\n")
            continue
        try:
            send_telegram(message)
        except Exception as exc:
            log(f"Erro ao enviar para o Telegram: {exc}")
            continue
        seen[post.id] = now.isoformat()
        sent += 1
        log(f"Enviada: {post.title[:80]} (r/{post.subreddit}, via {post.source})")
        save_state(seen, meta)                # grava a cada envio: nada se perde se a execução cair
        time.sleep(TELEGRAM_PAUSE)

    if not DRY_RUN:
        save_state(prune_seen(seen, now), meta)
    log(f"Concluído. Posts lidos: {len(posts)} | novos na janela: {len(fresh)} | vagas enviadas: {sent}")
    if errors and ok == 0:
        log("ATENÇÃO: nenhuma fonte respondeu nesta execução.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
