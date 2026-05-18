import requests

API_KEY = "3016c710cf4d9ca6f30f82eabefb7bd4"
headers = {"x-apisports-key": API_KEY}

r = requests.get(
    "https://v3.football.api-sports.io/odds?fixture=1379329",
    headers=headers
)

data = r.json()

for item in data.get("response", []):
    for book in item.get("bookmakers", []):
        print("Casa:", book["name"])
        for bet in book.get("bets", []):
            print("  Mercado:", bet["name"])
            for v in bet.get("values", []):
                print("    -", v.get("value"), ":", v.get("odd"))