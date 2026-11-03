import os
import requests
import xml.etree.ElementTree as ET

TOKEN = os.environ["TELEGRAM_TOKEN"]
CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]

SUBREDDITS = [
    "VideoEditor_forhire",
    "forhire",
    "CreatorServices",
    "VideoEditors",
    "VideoEditing"
]

KEYWORDS = [
    "hiring video editor",
    "looking for video editor",
    "video editor needed",
    "youtube editor",
    "short form editor",
    "shorts editor",
    "motion designer",
    "premiere pro",
    "after effects",
    "editor de video"
]

EXCLUDE = [
    "hire me",
    "i am a video editor",
    "portfolio",
    "unpaid",
    "free work",
    "course",
    "tutorial"
]

def send_telegram(message):
    url = f"https://api.telegram.org/bot{TOKEN}/sendMessage"
    requests.post(url, data={
        "chat_id": CHAT_ID,
        "text": message,
        "disable_web_page_preview": True
    }, timeout=20)

def main():
    found = 0

    for sub in SUBREDDITS:
        url = f"https://www.reddit.com/r/{sub}/new/.rss"

        try:
            response = requests.get(
                url,
                headers={"User-Agent": "RedditJobHunter/1.0"},
                timeout=20
            )
            response.raise_for_status()

            root = ET.fromstring(response.content)

            for item in root.findall(".//{http://www.w3.org/2005/Atom}entry"):
                title = item.findtext("{http://www.w3.org/2005/Atom}title", "")
                link = item.find("{http://www.w3.org/2005/Atom}link")

                if link is None:
                    continue

                post_url = link.attrib.get("href", "")
                text = title.lower()

                if any(word in text for word in EXCLUDE):
                    continue

                if not any(word in text for word in KEYWORDS):
                    continue

                message = (
                    "🎯 POSSÍVEL VAGA DE EDIÇÃO\n\n"
                    f"Subreddit: r/{sub}\n"
                    f"Título: {title}\n\n"
                    f"Link: {post_url}"
                )

                send_telegram(message)
                found += 1

        except Exception as e:
            print(f"Erro em r/{sub}: {e}")

    print(f"Monitoramento concluído. Vagas encontradas: {found}")

if __name__ == "__main__":
    main()
