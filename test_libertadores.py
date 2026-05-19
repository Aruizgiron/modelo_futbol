import requests

API_KEY = "3016c710cf4d9ca6f30f82eabefb7bd4"
BASE_URL = "https://v3.football.api-sports.io"
HEADERS = {"x-apisports-key": API_KEY}

ligas = [
    ("Copa Libertadores", 13, 2026),
    ("Copa Sudamericana", 11, 2026),
]

hoy = "2026-05-19"

for nombre, lid, season in ligas:
    url = f"{BASE_URL}/fixtures?league={lid}&season={season}&date={hoy}&timezone=America/Lima"
    r = requests.get(url, headers=HEADERS, timeout=15)
    data = r.json()
    resultados = data.get("results", 0)
    partidos = data.get("response", [])
    print(f"\n{'='*50}")
    print(f"{nombre} (id:{lid}, season:{season})")
    print(f"Resultados API: {resultados}")
    if partidos:
        for p in partidos:
            h = p["teams"]["home"]["name"]
            a = p["teams"]["away"]["name"]
            hora = p["fixture"]["date"]
            status = p["fixture"]["status"]["short"]
            print(f"  ⚽ {h} vs {a} | {hora} | {status}")
    else:
        print("  ❌ Sin partidos para esta fecha")
        # Buscar sin fecha para ver si la liga tiene datos
        url2 = f"{BASE_URL}/fixtures?league={lid}&season={season}&next=5"
        r2 = requests.get(url2, headers=HEADERS, timeout=15)
        data2 = r2.json()
        proximos = data2.get("response", [])
        if proximos:
            print(f"  📅 Próximos partidos en la liga:")
            for p in proximos[:3]:
                h = p["teams"]["home"]["name"]
                a = p["teams"]["away"]["name"]
                fecha = p["fixture"]["date"]
                print(f"     {h} vs {a} | {fecha}")
        else:
            print(f"  ⚠️ La liga no tiene partidos próximos en la API")
