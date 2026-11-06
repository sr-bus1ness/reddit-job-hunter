"""
Sr.Business Job-Bot
====================
Monitora subreddits e outras plataformas em busca de vagas de edição de vídeo
e envia ao Telegram.

Plataformas: Reddit, LinkedIn, InfoJobs, Workana, 99Freelas, ProductionHUB,
Mandy, Contra e QUALQUER feed RSS/Atom (Upwork, X/Twitter etc. via EXTRA_RSS_FEEDS).

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
  EXTRA_RSS_FEEDS     opcional, uma linha por feed no formato  Nome|https://url-do-feed
  DISABLE_SOURCES     opcional, chaves separadas por vírgula (ex.: "contra,mandy")
  REACTION_APPLIED / REACTION_DISCARD   emojis de reação (padrão 👍 / 👎)
  HIDE_BUTTONS_AFTER_CLICK=1   remove os botões depois do clique (padrão: mantém)

Teste das fontes novas (nada é enviado):  python main.py --test-sources
"""
from __future__ import annotations

import hashlib
import html
import json
import os
import re
import sys
import threading
import time
import unicodedata
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from urllib.parse import urljoin, urlparse
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
    # X/Twitter: a maioria dos tweets é de editores se oferecendo.
    "x",
    "twitter",
    "xtwitter",
}

# Subreddits dedicados a vagas/pedidos: contratação é implícita.
JOB_BOARD_SUBS = {
    "findvideoeditors",
    "hireaneditor",
    "videoeditingjobs",
    "videoeditingrequests",
    # Plataformas de vagas: todo anúncio já é uma contratação.
    "linkedin",
    "infojobs",
    "workana",
    "99freelas",
    "productionhub",
    "mandy",
    "contra",
    "upwork",
    "fiverr",
}

SEEN_FILE = os.environ.get("SEEN_FILE", "seen_posts.json")
SOURCE_MODE = os.environ.get("REDDIT_SOURCE", "auto").strip().lower()
DRY_RUN = os.environ.get("DRY_RUN") == "1"
DEBUG = os.environ.get("DEBUG") == "1"

# O primeiro horário de execução fica salvo em seen_posts.json (meta.started_at).
# Nas execuções seguintes, só buscamos posts desde a última varredura, com pequena
# sobreposição para não perder posts que apareçam atrasados no feed.
SCAN_OVERLAP = timedelta(minutes=10)
SEEN_RETENTION = timedelta(days=30)     # histórico de IDs e duplicatas já enviados
CLOCK_SKEW = timedelta(minutes=10)      # tolerância para relógios dessincronizados
ALERT_AFTER = timedelta(hours=3)        # avisa no Telegram se tudo falhar por este tempo
ALERT_EVERY = timedelta(hours=12)       # intervalo mínimo entre avisos

RSS_LIMIT = 50                         # reduz a leitura do feed agregado por ciclo
RSS_CHUNK = 5                           # tamanho dos grupos no fallback do RSS
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
    platform: str = "Reddit"      # nome exibido no Telegram
    company: str = ""
    location: str = ""
    dated: bool = True            # False = a plataforma não informa data/hora confiável


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
    # Pessoas procurando emprego/projetos para si (inglês, espanhol e português).
    r"\b(?:i am|i'm|im) (?:a |an )?(?:freelance |professional )?(?:video )?editors?\b",
    r"\bi edit\b[^.!?\n]{0,120}\b(?:videos?|reels?|shorts?|tiktoks?|clips?)\b",
    r"\b(?:looking for work as|seeking work as|looking for a job as)\b",
    r"\bseeking (?:a )?(?:job|position|employment)\b",
    r"\b(?:buscando|estoy buscando) (?:trabajo|empleo|proyectos?|clientes?|oportunidades)(?: como)?\b",
    r"\b(?:busco|buscamos) (?:trabajo|empleo|proyectos?|clientes?|oportunidades)\b",
    r"\b(?:estou )?procurando (?:trabalho|emprego|projetos?|clientes?|oportunidades)(?: como)?\b",
    r"\b(?:procuro|busco) (?:trabalho|emprego|projetos?|clientes?)\b",
    r"\b(?:soy|somos) (?:un |una )?(?:editor(?:a)? de video|editor de videos)\b",
    r"\b(?:sou|somos) (?:um |uma )?(?:editor(?:a)? de video|editor de videos)\b",
    r"\bhere(?:'s| is) my (?:portfolio|reel|showreel)\b",
    r"\bthis is my (?:portfolio|reel|showreel)\b",
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
    re.compile(r"\b(?:editor(?:es|a|as)? de (?:\w+ )?(?:videos?|reels?|shorts?|youtube)|"
               r"(?:edicao|edicion|montagem|montaje|montador(?:es|a|as)?) de (?:\w+ )?(?:videos?|reels?|shorts?)|"
               r"videomaker|videografo|editar videos?)\b"),
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
# IDIOMA
# ============================================================================
_LANGUAGE_PATTERNS = {
    "Inglês": re.compile(r"\b(?:i|the|and|for|you|your|we|our|with|looking|need|hiring|paid|budget|send|please|including|this|that)\b"),
    "Espanhol": re.compile(r"\b(?:el|los|las|del|que|para|con|busco|buscamos|necesito|necesitamos|trabajo|contratando|presupuesto|envia|envíame)\b"),
    "Português": re.compile(r"\b(?:os|das|dos|que|para|com|uma|estou|preciso|precisamos|procuro|procuramos|trabalho|contratando|orcamento|envie|voce|seu)\b"),
    "Francês": re.compile(r"\b(?:le|les|des|que|pour|avec|recherche|besoin|nous|vous|monteur|montage|bonjour|merci)\b"),
}


def get_language(title: str, body: str = "") -> str:
    """Identificação leve do idioma, sem dependências externas."""
    text = fold(f"{title} {body}")
    scores = {name: len(rx.findall(text)) for name, rx in _LANGUAGE_PATTERNS.items()}
    best = max(scores, key=scores.get)
    return best if scores[best] else "Não identificado"


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


def http_get(url: str, *, params: dict | None = None, headers: dict | None = None,
             retries: int = 2) -> requests.Response:
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
            resp = _SESSION.get(url, params=params, headers=headers, timeout=(10, 30))
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
        "limit": 50,
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
def collect_posts(now: datetime, since: datetime, mode: str = SOURCE_MODE):
    """Devolve (posts_por_id, fontes_ok, erros), considerando o cursor informado."""
    posts: dict[str, Post] = {}
    errors: list[str] = []
    ok = 0
    pending: list[str] = []

    def add(batch: list[Post]):
        # Descarta imediatamente qualquer post anterior ao cursor/startup.
        for p in batch:
            if p.created >= since:
                posts.setdefault(p.id, p)

    if mode in ("auto", "rss"):
        try:
            batch = fetch_rss(SUBREDDITS)
            add(batch)
            ok += 1
            new_in_feed = sum(p.created >= since for p in batch)
            log(f"RSS: {new_in_feed} posts após o cursor (limite {RSS_LIMIT}) em 1 requisição.")
            # Se o feed atingiu o limite e todos os itens são posteriores ao cursor,
            # ele pode ter sido truncado antes de alcançar o início da varredura.
            oldest = min((p.created for p in batch), default=None)
            if len(batch) >= RSS_LIMIT and oldest and oldest > since:
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
                        count_new = sum(p.created >= since for p in batch)
                        log(f"RSS grupo {chunk}: {count_new} posts após o cursor.")
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
# OUTRAS PLATAFORMAS
# ============================================================================
# Cada fonte devolve uma lista de Post; o resto do fluxo (filtro, deduplicação,
# Telegram) é o mesmo do Reddit. Sites sem data confiável usam dated=False: na
# PRIMEIRA varredura de cada fonte as vagas que já estão no ar são só registradas
# (não enviadas), para você não receber centenas de mensagens de uma vez.
BROWSER_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9,pt-BR;q=0.8",
}
DISABLED_SOURCES = {s.strip().lower() for s in os.environ.get("DISABLE_SOURCES", "").split(",") if s.strip()}
SOURCE_ALERT_AFTER = timedelta(hours=6)   # avisa se uma fonte ficar fora do ar por este tempo
SOURCE_ALERT_EVERY = timedelta(hours=24)  # no máximo um aviso de fontes por dia


@dataclass(frozen=True)
class Board:
    """Site de vagas lido pelos links da página de busca (sem depender de CSS)."""
    key: str                 # identificador interno (também usado pelo filtro)
    name: str                # nome mostrado no Telegram
    urls: tuple              # páginas de busca consultadas a cada varredura
    link_re: str             # regex do link de uma vaga; o grupo "id" é o identificador
    every: int = 15          # minutos entre varreduras desta fonte
    experimental: bool = False


# Se um site mudar de endereço, é aqui que se corrige (URL de busca e/ou link_re).
BOARDS = [
    Board("workana", "Workana",
          ("https://www.workana.com/en/jobs?query=video+editor&publication=1d",
           "https://www.workana.com/pt/jobs?query=edi%C3%A7%C3%A3o+de+v%C3%ADdeo&publication=1d"),
          r"/job/(?P<id>[A-Za-z0-9_-]+)"),
    Board("99freelas", "99Freelas",
          ("https://www.99freelas.com.br/projects?q=edi%C3%A7%C3%A3o+de+v%C3%ADdeo",
           "https://www.99freelas.com.br/projects?q=editor+de+video"),
          r"/project/(?P<id>[A-Za-z0-9_-]*\d)"),
    Board("infojobs", "InfoJobs",
          ("https://www.infojobs.com.br/vagas-de-emprego-editor-de-video.aspx",
           "https://www.infojobs.com.br/empregos.aspx?palavrachave=edicao+de+video"),
          r"/vaga-de-(?P<id>[A-Za-z0-9_%.-]+?)\.aspx", experimental=True),
    Board("productionhub", "ProductionHUB",
          ("https://www.productionhub.com/jobs?keywords=video+editor",),
          r"/jobs?/(?P<id>[A-Za-z0-9_-]*\d[A-Za-z0-9_-]*)", experimental=True),
    Board("mandy", "Mandy",
          ("https://www.mandy.com/jobs?keywords=video+editor",),
          r"/jobs?/(?P<id>[A-Za-z0-9_-]*\d[A-Za-z0-9_-]*)", experimental=True),
    Board("contra", "Contra",
          ("https://contra.com/opportunities",),
          r"/opportunity/(?P<id>[A-Za-z0-9_-]+)", experimental=True),
]

_GENERIC_LINK_TEXT = {"apply", "apply now", "view job", "view details", "see more", "read more",
                      "ver mais", "ver detalhes", "saiba mais", "candidatar-se", "more details"}


class _AnchorParser(HTMLParser):
    """Coleta (href, texto) de todos os links da página."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.anchors: list[tuple[str, str]] = []
        self._href: str | None = None
        self._buf: list[str] = []
        self._skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip += 1
        elif tag == "a":
            self._flush()
            self._href = dict(attrs).get("href") or ""
            self._buf = []

    def handle_endtag(self, tag):
        if tag in ("script", "style") and self._skip:
            self._skip -= 1
        elif tag == "a":
            self._flush()

    def handle_data(self, data):
        if self._href is not None and not self._skip:
            self._buf.append(data)

    def _flush(self):
        if self._href is not None:
            self.anchors.append((self._href, re.sub(r"\s+", " ", " ".join(self._buf)).strip()))
        self._href, self._buf = None, []

    def close(self):
        super().close()
        self._flush()


def extract_board_links(page: str, base_url: str, link_re: str) -> list[tuple[str, str, str]]:
    """Devolve [(id, título, url)] para os links que casam com link_re."""
    parser = _AnchorParser()
    parser.feed(page or "")
    parser.close()
    rx = re.compile(link_re)
    best: dict[str, tuple[str, str]] = {}
    for href, text in parser.anchors:
        if not href or href.startswith(("javascript:", "mailto:", "#")):
            continue
        full = urljoin(base_url, html.unescape(href)).split("#")[0]
        m = rx.search(full)
        if not m:
            continue
        text = text[:200]
        if len(text) < 8 or fold(text) in _GENERIC_LINK_TEXT:
            continue
        pid = m.group("id")
        # vários links levam à mesma vaga (imagem, título, "ver mais"): fica o texto mais curto
        if pid not in best or len(text) < len(best[pid][0]):
            best[pid] = (text, full)
    return [(pid, title, url) for pid, (title, url) in best.items()]


def fetch_board(board: Board) -> list[Post]:
    now = utc_now()
    found: dict[str, tuple[str, str]] = {}
    errors: list[str] = []
    answered = 0
    for url in board.urls:
        try:
            resp = http_get(url, headers=BROWSER_HEADERS)
        except FetchError as exc:
            errors.append(str(exc))
            continue
        answered += 1
        for pid, title, link in extract_board_links(resp.text, url, board.link_re):
            found.setdefault(pid, (title, link))
        time.sleep(1)
    if not answered:
        raise FetchError("; ".join(dict.fromkeys(errors)) or "sem resposta")
    return [
        Post(id=f"{board.key}-{pid}", title=title, text="", url=link, subreddit=board.key,
             created=now, source="html", platform=board.name, dated=False)
        for pid, (title, link) in found.items()
    ]


# --- LinkedIn (endpoint público de vagas, sem login) ---------------------------
LINKEDIN_URL = "https://www.linkedin.com/jobs-guest/jobs/api/seeMoreJobPostings/search"
LINKEDIN_QUERIES = ("video editor", "editor de vídeo", "short form video editor")


def parse_linkedin(markup: str) -> list[Post]:
    now = utc_now()
    posts: list[Post] = []
    for card in re.findall(r"<li\b.*?</li>", markup or "", re.S):
        href = re.search(r'href="([^"]*?/jobs/view/[^"]*)"', card)
        if not href:
            continue
        m = re.search(r"/jobs/view/(?:[^/?\"]*?-)?(\d{6,})", html.unescape(href.group(1)))
        title = re.search(r"<h3[^>]*>(.*?)</h3>", card, re.S)
        if not m or not title:
            continue
        company = re.search(r"<h4[^>]*>(.*?)</h4>", card, re.S)
        place = re.search(r"job-search-card__location[^>]*>(.*?)</span>", card, re.S)
        posts.append(Post(
            id=f"linkedin-{m.group(1)}",
            title=clean_html(title.group(1)),
            text="",
            url=f"https://www.linkedin.com/jobs/view/{m.group(1)}",
            subreddit="linkedin",
            created=now,
            source="html",
            platform="LinkedIn",
            company=clean_html(company.group(1)) if company else "",
            location=clean_html(place.group(1)) if place else "",
            dated=False,    # o LinkedIn só informa a data (sem hora)
        ))
    return posts


def fetch_linkedin() -> list[Post]:
    found: dict[str, Post] = {}
    errors: list[str] = []
    answered = 0
    for keywords in LINKEDIN_QUERIES:
        try:
            resp = http_get(LINKEDIN_URL, headers=BROWSER_HEADERS, params={
                "keywords": keywords, "location": "Worldwide",
                "f_TPR": "r86400", "sortBy": "DD", "start": 0,
            })
        except FetchError as exc:
            errors.append(str(exc))
            continue
        answered += 1
        for post in parse_linkedin(resp.text):
            found.setdefault(post.id, post)
        time.sleep(2)
    if not answered:
        raise FetchError("; ".join(dict.fromkeys(errors)) or "sem resposta")
    return list(found.values())


# --- Feeds RSS/Atom genéricos (Upwork, X/Twitter e qualquer outro) ---------------
def extra_feeds() -> list[tuple[str, str, str]]:
    """Lê EXTRA_RSS_FEEDS: uma linha por feed, no formato  Nome|https://url"""
    feeds = []
    for line in os.environ.get("EXTRA_RSS_FEEDS", "").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        label, _, url = line.partition("|")
        label, url = label.strip(), url.strip()
        if not label or not url.startswith(("http://", "https://")):
            log(f"EXTRA_RSS_FEEDS: linha ignorada (use Nome|https://url): {label[:30]!r}")
            continue
        feeds.append((re.sub(r"[^a-z0-9]+", "", fold(label)) or "feed", label, url))
    return feeds


def _ft(entry, name: str) -> str:
    return (entry.findtext(name, "") or entry.findtext(f"a:{name}", "", _ATOM) or "").strip()


def parse_generic_feed(content: bytes, key: str, label: str) -> list[Post]:
    try:
        root = ET.fromstring(content)
    except ET.ParseError as exc:
        raise FetchError(f"resposta não é XML válido ({exc})", 200)
    now = utc_now()
    posts: list[Post] = []
    for entry in (root.findall(".//item") or root.findall(".//a:entry", _ATOM)):
        link = _ft(entry, "link")
        if not link:
            atom_link = entry.find("a:link", _ATOM)
            link = atom_link.attrib.get("href", "") if atom_link is not None else ""
        title = html.unescape(_ft(entry, "title"))
        if not link or not title:
            continue
        guid = _ft(entry, "guid") or _ft(entry, "id") or link
        raw_date = (_ft(entry, "pubDate") or _ft(entry, "published") or _ft(entry, "updated")
                    or _ft(entry, "{http://purl.org/dc/elements/1.1/}date"))
        created = parse_date(raw_date)
        body = (_ft(entry, "description") or _ft(entry, "content") or _ft(entry, "summary")
                or _ft(entry, "{http://purl.org/rss/1.0/modules/content/}encoded"))
        posts.append(Post(
            id=f"{key}-{hashlib.sha1(guid.encode('utf-8')).hexdigest()[:16]}",
            title=title,
            text=clean_html(body),
            url=link,
            subreddit=key,
            created=created or now,
            source="feed",
            platform=label,
            dated=created is not None,
        ))
    return posts


def fetch_feed(key: str, label: str, url: str) -> list[Post]:
    return parse_generic_feed(http_get(url, headers=BROWSER_HEADERS).content, key, label)


# --- orquestração -----------------------------------------------------------------
def build_fetchers() -> list[tuple[str, str, int, object]]:
    """[(chave, nome, minutos entre varreduras, função)] de todas as fontes extras."""
    fetchers = [("linkedin", "LinkedIn", 20, fetch_linkedin)]
    for board in BOARDS:
        fetchers.append((board.key, board.name, board.every, lambda b=board: fetch_board(b)))
    for key, label, url in extra_feeds():
        fetchers.append((key, label, 10, lambda k=key, l=label, u=url: fetch_feed(k, l, u)))
    return [f for f in fetchers if f[0] not in DISABLED_SOURCES]


def collect_extra(now: datetime, meta: dict, force: bool = False):
    """Roda as fontes extras que já estão no horário. Devolve (posts, resultados)."""
    posts: dict[str, Post] = {}
    results: dict[str, tuple[str, bool, str]] = {}
    last_runs = meta.setdefault("source_last_run", {})
    for key, name, every, fetch in build_fetchers():
        last = parse_date(last_runs.get(key))
        if not force and last and now - last < timedelta(minutes=every):
            continue
        if time_left() <= 20:
            log("Orçamento de tempo quase esgotado; fontes restantes ficam para o próximo ciclo.")
            break
        last_runs[key] = now.isoformat()      # conta a tentativa, para não insistir em fonte bloqueada
        try:
            batch = fetch()
        except FetchError as exc:
            results[key] = (name, False, str(exc))
            log(f"{name}: falhou ({exc})")
            continue
        except Exception as exc:              # HTML inesperado não pode derrubar o ciclo todo
            results[key] = (name, False, f"erro inesperado ({type(exc).__name__})")
            log(f"{name}: erro inesperado ({type(exc).__name__}: {exc})")
            continue
        results[key] = (name, True, "")
        for post in batch:
            posts.setdefault(post.id, post)
        log(f"{name}: {len(batch)} vagas listadas.")
    return posts, results


def update_source_health(meta: dict, results: dict, now: datetime) -> None:
    """Fontes extras são frágeis: avisa no Telegram (1x/dia) se alguma ficar fora do ar."""
    health = meta.setdefault("source_health", {})
    known = {f[0] for f in build_fetchers()}
    for key in [k for k in health if k not in known]:
        health.pop(key)
    for key, (name, ok, error) in results.items():
        entry = health.setdefault(key, {})
        entry["name"] = name
        if ok:
            entry.pop("failing_since", None)
            entry.pop("error", None)
        else:
            entry.setdefault("failing_since", now.isoformat())
            entry["error"] = error[:80]
    down = []
    for entry in health.values():
        since = parse_date(entry.get("failing_since"))
        if since and now - since >= SOURCE_ALERT_AFTER:
            down.append(f"• {entry.get('name', '?')}: {entry.get('error', 'sem resposta')}")
    last_alert = parse_date(meta.get("last_sources_alert"))
    if down and not DRY_RUN and (not last_alert or now - last_alert >= SOURCE_ALERT_EVERY):
        try:
            send_telegram("⚠️ Sr.Business Job-Bot: fontes sem resposta há mais de "
                          f"{int(SOURCE_ALERT_AFTER.total_seconds() // 3600)}h:\n" + "\n".join(down))
            meta["last_sources_alert"] = now.isoformat()
        except Exception as exc:
            log(f"Não consegui enviar o aviso de fontes: {exc}")


def test_sources() -> int:
    """python main.py --test-sources : mostra o que cada fonte extra consegue ler agora."""
    log("Teste das fontes extras (nada é enviado ao Telegram, nada é gravado).")
    experimental = {b.key for b in BOARDS if b.experimental}
    for key, name, _every, fetch in build_fetchers():
        tag = " (experimental)" if key in experimental else ""
        try:
            batch = fetch()
        except FetchError as exc:
            log(f"[FALHOU] {name}{tag}: {exc}")
            continue
        except Exception as exc:
            log(f"[ERRO]   {name}{tag}: {type(exc).__name__}: {exc}")
            continue
        passing = sum(classify(p).accepted for p in batch)
        log(f"[OK]     {name}{tag}: {len(batch)} itens lidos, {passing} passariam no filtro.")
        for post in batch[:3]:
            log(f"           - {post.title[:80]!r} -> {classify(post).reason}")
        if not batch:
            log("           (nenhum link reconhecido: o site pode ter bloqueado o IP ou mudado de layout)")
        time.sleep(1)
    return 0


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
def send_telegram(message: str, post_id: str | None = None, html_mode: bool = False) -> None:
    """Envia a vaga com dois botões compactos: 👎 e 👍 (viram uma reação ao serem tocados)."""
    token = os.environ.get("TELEGRAM_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat_id:
        raise RuntimeError("TELEGRAM_TOKEN/TELEGRAM_CHAT_ID não configurados.")
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {
        "chat_id": chat_id,
        "text": message,
        "disable_web_page_preview": True,
    }
    if html_mode:
        payload["parse_mode"] = "HTML"
    if post_id:
        payload["reply_markup"] = json.dumps({
            "inline_keyboard": [[
                {"text": "👎", "callback_data": "discard"},
                {"text": "👍", "callback_data": "applied"},
            ]]
        }, ensure_ascii=False)

    for attempt in range(3):
        try:
            resp = requests.post(url, data=payload, timeout=20)
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



# ==========================================================================
# BOTÕES DO TELEGRAM -> REAÇÃO NA PRÓPRIA MENSAGEM
# ==========================================================================
# O Telegram só aceita um conjunto fixo de emojis como reação. Botão 👍 reage com 👍 e
# botão 👎 reage com 👎. Dá para trocar por qualquer emoji permitido
# (👍 👎 🔥 🏆 💯 👌 🤝 🙈 😴 ...) pelas variáveis REACTION_APPLIED / REACTION_DISCARD.
REACTION_APPLIED = os.environ.get("REACTION_APPLIED", "👍")
REACTION_DISCARD = os.environ.get("REACTION_DISCARD", "👎")
HIDE_BUTTONS_AFTER_CLICK = os.environ.get("HIDE_BUTTONS_AFTER_CLICK") == "1"

# Sessão persistente: reaproveita a conexão HTTPS e evita o handshake a cada clique.
_TG_SESSION = requests.Session()


def _telegram_api(method: str, payload: dict, timeout: int = 20) -> dict | None:
    """Chama a API sem expor o token em logs ou mensagens de erro."""
    token = os.environ.get("TELEGRAM_TOKEN", "")
    if not token:
        return None
    try:
        response = _TG_SESSION.post(
            f"https://api.telegram.org/bot{token}/{method}",
            json=payload,
            timeout=timeout,
        )
        data = response.json()
    except (requests.RequestException, ValueError):
        log(f"Botões: falha de comunicação ao chamar {method}.")
        return None
    if response.status_code != 200 or not data.get("ok"):
        # Não imprime a resposta completa: ela pode conter dados desnecessários.
        reason = str(data.get("description", ""))[:120] if isinstance(data, dict) else ""
        log(f"Botões: Telegram recusou {method} (HTTP {response.status_code}) {reason}")
        return None
    return data


def _handle_telegram_callback(callback: dict) -> None:
    """Reage à mensagem original com o emoji escolhido. Não edita texto nem envia nada."""
    callback_id = str(callback.get("id") or "")
    # Aceita também o formato antigo ("applied:<id>") de mensagens já enviadas.
    match = re.fullmatch(r"(applied|discard)(?::[A-Za-z0-9_-]{1,64})?", str(callback.get("data") or ""))

    message = callback.get("message") or {}
    chat = message.get("chat") or {}
    chat_id = chat.get("id")
    message_id = message.get("message_id")

    # Encerra o "carregando" do botão em paralelo, sem texto, alerta ou notificação.
    answer = None
    if callback_id:
        answer = threading.Thread(
            target=_telegram_api,
            args=("answerCallbackQuery", {"callback_query_id": callback_id, "show_alert": False}),
            daemon=True,
        )
        answer.start()

    if match and chat_id is not None and message_id is not None \
            and str(chat_id) == str(os.environ.get("TELEGRAM_CHAT_ID", "")):
        emoji = REACTION_APPLIED if match.group(1) == "applied" else REACTION_DISCARD
        _telegram_api("setMessageReaction", {
            "chat_id": chat_id,
            "message_id": message_id,
            "reaction": [{"type": "emoji", "emoji": emoji}],
        })
        if HIDE_BUTTONS_AFTER_CLICK:
            _telegram_api("editMessageReplyMarkup", {
                "chat_id": chat_id,
                "message_id": message_id,
                "reply_markup": {"inline_keyboard": []},
            })

    if answer:
        answer.join(timeout=5)


def telegram_buttons_listener() -> int:
    """Escuta cliques continuamente; roda em segundo plano no workflow."""
    token = os.environ.get("TELEGRAM_TOKEN", "")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "")
    if not token or not chat_id:
        log("Botões: TELEGRAM_TOKEN/TELEGRAM_CHAT_ID não configurados.")
        return 2

    api_url = f"https://api.telegram.org/bot{token}/getUpdates"
    offset: int | None = None
    log("Botões: listener iniciado (sem respostas ou notificações).")

    while True:
        params = {
            "timeout": 25,
            "allowed_updates": '["callback_query"]',
        }
        if offset is not None:
            params["offset"] = offset
        try:
            response = _TG_SESSION.get(api_url, params=params, timeout=35)
            data = response.json()
        except (requests.RequestException, ValueError):
            log("Botões: falha ao consultar cliques; nova tentativa em 5 segundos.")
            time.sleep(5)
            continue

        if response.status_code == 409:
            log("Botões: conflito com outro processo usando getUpdates.")
            time.sleep(10)
            continue
        if response.status_code == 429:
            retry = (data.get("parameters") or {}).get("retry_after", 5)
            try:
                time.sleep(min(int(retry) + 1, 30))
            except (TypeError, ValueError):
                time.sleep(6)
            continue
        if response.status_code != 200 or not data.get("ok"):
            log(f"Botões: getUpdates falhou (HTTP {response.status_code}).")
            time.sleep(5)
            continue

        for update in data.get("result", []):
            callback = update.get("callback_query")
            if callback:
                _handle_telegram_callback(callback)
            update_id = update.get("update_id")
            if isinstance(update_id, int):
                offset = update_id + 1


LINE = "-" * 24


def script_bold(text: str) -> str:
    """Letras em 'bold script' (Unicode): o Telegram não troca de fonte, então usamos estes símbolos."""
    out = []
    for ch in text:
        if "A" <= ch <= "Z":
            out.append(chr(0x1D4D0 + ord(ch) - ord("A")))
        elif "a" <= ch <= "z":
            out.append(chr(0x1D4EA + ord(ch) - ord("a")))
        else:
            out.append(ch)
    return "".join(out)


BOT_NAME = "Sr.Business Job-Bot"


def build_message(post: Post) -> str:
    """Mensagem em HTML (enviada com parse_mode=HTML): todo texto de terceiros é escapado."""
    esc = lambda value: html.escape(str(value), quote=False)
    title = re.sub(r"\s+", " ", post.title).strip()
    if len(title) > 250:
        title = title[:247] + "..."
    full_text = f"{post.title} {post.text}"
    local_date = post.created.astimezone(ZoneInfo("America/Sao_Paulo")).strftime("%d/%m/%Y às %H:%M")
    origin = f"Reddit · r/{post.subreddit}" if post.platform == "Reddit" else post.platform
    lines = [
        LINE,
        f"<b>{script_bold(BOT_NAME)}</b>",
        LINE,
        "",
        f"📡 {esc(origin)}",
        f"📌 {esc(title)}",
    ]
    if post.company:
        lines.append(f"🏢 {esc(post.company)}")
    if post.location:
        lines.append(f"📍 {esc(post.location)}")
    lines += [
        f"💰 {esc(get_value(full_text))}",
        f"🎬 {esc(get_niche(post.title, post.text))}",
        f"🌐 {esc(get_language(post.title, post.text))}",
        f"🕒 {local_date}",
        LINE,
        esc(post.url),
        LINE,
    ]
    return "\n".join(lines)



def post_fingerprints(post: Post) -> set[str]:
    """Chaves para reconhecer a mesma vaga mesmo com título diferente entre subreddits."""
    import hashlib

    title = fold_body(post.title)
    body = re.sub(r"\s+", " ", fold_body(post.text)).strip()

    def digest(value: str) -> str:
        return hashlib.sha256(value.encode("utf-8")).hexdigest()

    # Listagens sem descrição: títulos iguais ("Video Editor") de vagas diferentes não são duplicata.
    url_key = f"|{post.url}" if len(body) < 40 else ""
    fingerprints = {digest(f"title+body:{title}|{body}{url_key}")}
    # Crossposts às vezes recebem títulos diferentes, mas mantêm a descrição inteira.
    # A chave extra só é usada quando há uma descrição longa e relativamente específica.
    if len(body) >= 180 and len(body.split()) >= 30:
        fingerprints.add(digest(f"body:{body}"))
    return fingerprints


def prune_fingerprints(meta: dict, now: datetime) -> None:
    fingerprints = meta.get("sent_fingerprints")
    if not isinstance(fingerprints, dict):
        meta["sent_fingerprints"] = {}
        return
    limit = now - SEEN_RETENTION
    meta["sent_fingerprints"] = {
        key: value for key, value in fingerprints.items()
        if isinstance(value, str) and (parse_date(value) or datetime.min.replace(tzinfo=timezone.utc)) >= limit
    }


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
                "⚠️ Sr.Business Job-Bot: sem acesso ao Reddit desde "
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
    seen, meta = load_state()

    # Esse marco é criado uma única vez e persiste entre ciclos/reexecuções do workflow.
    started_at = parse_date(meta.get("started_at"))
    if started_at is None:
        started_at = now
        meta["started_at"] = started_at.isoformat()
        log(f"Primeiro início registrado: {started_at.astimezone(ZoneInfo('America/Sao_Paulo')):%d/%m/%Y %H:%M:%S}")

    # Cursor incremental: reavalia apenas uma pequena sobreposição para capturar
    # posts que o Reddit/arquivo possam disponibilizar com alguns minutos de atraso.
    last_scan = parse_date(meta.get("last_scan_at")) or started_at
    scan_since = max(started_at, last_scan - SCAN_OVERLAP)

    posts, ok, errors = collect_posts(now, scan_since)
    update_health(meta, ok, errors, now)

    # Outras plataformas (cada uma respeita o seu próprio intervalo entre varreduras).
    extra_posts, extra_results = collect_extra(now, meta)
    update_source_health(meta, extra_results, now)
    for pid, post in extra_posts.items():
        posts.setdefault(pid, post)
        if not post.dated and pid in seen:
            seen[pid] = now.isoformat()       # ainda no ar: mantém no histórico
    seeded = set(meta.get("seeded_sources") or [])
    seeded_now: dict[str, int] = {}

    fresh = [
        p for p in posts.values()
        if scan_since <= p.created <= now + CLOCK_SKEW and p.id not in seen
    ]
    fresh.sort(key=lambda p: p.created)       # do mais antigo ao mais novo

    sent = 0
    sent_fingerprints = meta.setdefault("sent_fingerprints", {})
    batch_fingerprints: set[str] = set()
    for post in fresh:
        # Primeira varredura de uma fonte sem data: só registra o que já estava no ar.
        if not post.dated and post.subreddit not in seeded and not DRY_RUN:
            seen[post.id] = now.isoformat()
            seeded_now[post.subreddit] = seeded_now.get(post.subreddit, 0) + 1
            continue
        fingerprints = post_fingerprints(post)
        if fingerprints & (set(sent_fingerprints) | batch_fingerprints):
            debug(f"[duplicada] {post.platform}/{post.subreddit}: {post.title[:80]!r} -> vaga já enviada em outro post/subreddit")
            continue

        decision = classify(post)
        if not decision.accepted:
            debug(f"[rejeitada] {post.platform}/{post.subreddit}: {post.title[:80]!r} -> {decision.reason}")
            continue
        message = build_message(post)
        if DRY_RUN:
            log(f"[DRY_RUN] ({decision.reason})\n{message}\n")
            batch_fingerprints.update(fingerprints)
            continue
        try:
            send_telegram(message, post_id=post.id, html_mode=True)
        except Exception as exc:
            log(f"Erro ao enviar para o Telegram: {exc}")
            continue
        seen[post.id] = now.isoformat()
        for fingerprint in fingerprints:
            sent_fingerprints[fingerprint] = now.isoformat()
        batch_fingerprints.update(fingerprints)
        sent += 1
        log(f"Enviada: {post.title[:80]} ({post.platform}"
            f"{' r/' + post.subreddit if post.platform == 'Reddit' else ''}, via {post.source})")
        save_state(seen, meta)                # grava a cada envio: nada se perde se a execução cair
        time.sleep(TELEGRAM_PAUSE)

    # Só avança o cursor quando ao menos uma fonte respondeu. Se tudo falhar,
    # a próxima execução retenta o mesmo intervalo em vez de pular vagas.
    if ok > 0:
        meta["last_scan_at"] = now.isoformat()

    if not DRY_RUN:
        for key, count in seeded_now.items():
            log(f"{key}: primeira varredura, {count} vagas já existentes registradas sem envio.")
        seeded.update(key for key, (_name, answered, _err) in extra_results.items() if answered)
        meta["seeded_sources"] = sorted(seeded)

    if not DRY_RUN:
        seen = prune_seen(seen, now)
        prune_fingerprints(meta, now)
        save_state(seen, meta)

    log(
        f"Concluído. Posts após o cursor: {len(posts)} | "
        f"novos desde o último cursor: {len(fresh)} | vagas enviadas: {sent}"
    )
    log(f"Monitorando posts publicados a partir de {started_at.astimezone(ZoneInfo('America/Sao_Paulo')):%d/%m/%Y %H:%M:%S}.")
    if errors and ok == 0:
        log("ATENÇÃO: nenhuma fonte respondeu nesta execução.")
    return 0



if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--buttons-listener":
        sys.exit(telegram_buttons_listener())
    if len(sys.argv) > 1 and sys.argv[1] == "--test-sources":
        sys.exit(test_sources())
    sys.exit(main())
