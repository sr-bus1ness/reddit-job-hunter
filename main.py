
import os
import re
import json
import requests
import xml.etree.ElementTree as ET

from datetime import datetime, timezone, timedelta
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from zoneinfo import ZoneInfo

TOKEN = os.environ["TELEGRAM_TOKEN"]
CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]

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
    "forhire"
]

EXCLUDE = [
    "i am a video editor",
    "hire me",
    "portfolio",
    "free work",
    "unpaid",
    "course",
    "tutorial"
]

HIRING_TERMS = [
    "hiring", "looking for", "looking to hire",
    "need a video editor", "need an editor",
    "seeking", "wanted", "editor needed",
    "looking for editor", "need someone to edit",
    "busco editor", "se busca editor",
    "buscando editor", "contratando editor",
    "paid editing"
]

ROLE_TERMS = [
    "video editor", "video editing", "editor",
    "premiere", "after effects", "shorts",
    "youtube", "reels", "tiktok", "documentary",
    "motion design", "podcast", "video"
]

SEEN_FILE = "seen_posts.json"
WINDOW = timedelta(hours=24)

class TextExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts = []

    def handle_data(self, data):
        self.parts.append(data)

    def get_text(self):
        return " ".join(self.parts)


def clean_html(value):
    parser = TextExtractor()
    parser.feed(value or "")
    return parser.get_text()


def parse_date(value):
    if not value:
        return None

    try:
        date = parsedate_to_datetime(value)
    except Exception:
        try:
            date = datetime.fromisoformat(value.replace("Z", "+00:00"))
        except Exception:
            return None

    if date.tzinfo is None:
        date = date.replace(tzinfo=timezone.utc)

    return date.astimezone(timezone.utc)


def get_value(text):
    patterns = [
        r'(?:US\$|\$|USD)\s?\d[\d,]*(?:\.\d{1,2})?(?:\s*(?:-|to)\s*(?:US\$|\$|USD)?\s?\d[\d,]*(?:\.\d{1,2})?)?',
        r'(?:€|EUR|£|GBP|R\$)\s?\d[\d.,]*(?:\s*(?:-|to)\s*\d[\d.,]*)?',
        r'\b\d[\d,]*(?:\.\d{1,2})?\s?(?:dollars?|euros?|pounds?|per hour|/hr|hourly|per video|/video|per month|/month|monthly|weekly)\b'
    ]

    for pattern in patterns:
        match = re.search(pattern, text, re.IGNORECASE)
        if match:
            return match.group(0).strip()

    return "Não informado"


def get_niche(text):
    categories = [
        ("Shorts / Reels / TikTok", ["shorts", "reels", "tiktok", "short form"]),
        ("YouTube / Long-form", ["youtube", "long form", "long-form"]),
        ("Gaming", ["gaming", "gamer", "minecraft", "roblox", "gameplay"]),
        ("Documentário", ["documentary", "documentary", "docuseries"]),
        ("Podcast", ["podcast"]),
        ("Motion Design", ["motion design", "motion graphics", "after effects"]),
        ("Publicidade / Marketing", ["ads", "advertising", "marketing", "commercial"]),
        ("Anime / Recap", ["anime", "naruto", "recap", "manga"]),
        ("Corporativo", ["corporate", "business", "company"])
    ]

    for name, words in categories:
        if any(word in text for word in words):
            return name

    return "Não identificado"


def load_seen():
    try:
        with open(SEEN_FILE, "r", encoding="utf-8") as file:
            return json.load(file)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_seen(seen):
    with open(SEEN_FILE, "w", encoding="utf-8") as file:
        json.dump(seen, file, indent=2)


def send_telegram(message):
    url = f"https://api.telegram.org/bot{TOKEN}/sendMessage"

    response = requests.post(
        url,
        data={
            "chat_id": CHAT_ID,
            "text": message,
            "disable_web_page_preview": True
        },
        timeout=20
    )

    response.raise_for_status()

    if not response.json().get("ok"):
        raise RuntimeError("Telegram não confirmou o envio.")


def main():
    now = datetime.now(timezone.utc)
    cutoff = now - WINDOW

    seen = load_seen()
    sent_count = 0

    for sub in SUBREDDITS:
        url = f"https://www.reddit.com/r/{sub}/new/.rss?limit=100"

        try:
            response = requests.get(
                url,
                headers={"User-Agent": "BotJobVideoEditor/1.0"},
                timeout=25
            )
            response.raise_for_status()

            root = ET.fromstring(response.content)
            ns = {"a": "http://www.w3.org/2005/Atom"}

            for item in root.findall("a:entry", ns):
                title = item.findtext("a:title", "", ns)
                link = item.find("a:link", ns)
                post_id = item.findtext("a:id", "", ns)

                published = (
                    item.findtext("a:published", "", ns)
                    or item.findtext("a:updated", "", ns)
                )

                post_date = parse_date(published)

                if not post_date or post_date < cutoff or post_date > now:
                    continue

                if link is None:
                    continue

                post_url = link.attrib.get("href", "")
                post_id = post_id or post_url

                if not post_id or post_id in seen:
                    continue

                content = item.findtext("a:content", "", ns)
                summary = item.findtext("a:summary", "", ns)
                description = clean_html(content or summary)

                full_text = f"{title} {description}".lower()

                if any(word in full_text for word in EXCLUDE):
                    continue

                has_hiring = any(term in full_text for term in HIRING_TERMS)
                has_role = any(term in full_text for term in ROLE_TERMS)

                if not (has_hiring and has_role):
                    continue

                value = get_value(full_text)
                niche = get_niche(full_text)

                local_date = post_date.astimezone(
                    ZoneInfo("America/Sao_Paulo")
                ).strftime("%d/%m/%Y às %H:%M")

                message = (
                    "🤖 BOT JOB VIDEO EDITOR\n\n"
                    f"📌 VAGA: {title}\n"
                    f"💰 VALOR: {value}\n"
                    f"🎬 NICHO: {niche}\n"
                    f"📂 SUBREDDIT: r/{sub}\n"
                    f"🕒 PUBLICADA: {local_date}\n\n"
                    f"🔗 {post_url}"
                )

                try:
                    send_telegram(message)
                    seen[post_id] = now.isoformat()
                    sent_count += 1
                    print(f"Enviada: {title}")
                except Exception as error:
                    print(f"Erro ao enviar para Telegram: {error}")

        except Exception as error:
            print(f"Erro em r/{sub}: {error}")

    # Mantém apenas os registros dos últimos 7 dias.
    seven_days_ago = now - timedelta(days=7)
    seen = {
        post_id: sent_at
        for post_id, sent_at in seen.items()
        if parse_date(sent_at) and parse_date(sent_at) >= seven_days_ago
    }

    save_seen(seen)
    print(f"Monitoramento concluído. Novas vagas enviadas: {sent_count}")


if __name__ == "__main__":
    main()
