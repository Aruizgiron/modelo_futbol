"""
reconstruir_dia22.py
HarryNine V14 — Reconstruccion de picks del 22 de mayo 2026.

Los picks del 22 se perdieron (mismo problema: git reset --hard sin
.gitignore). Se reinsertan desde los PDFs:
  - RESUMEN PREMATCH 22/05 13:46 (14 picks, version mas completa)
  - RESUMEN LIVE 22/05 13:46 (23 picks)
  - RESUMEN COMBINADAS 22/05 09:56 (3 combinadas)

- No duplica: si un pick ya existe, lo salta.
- Escritura atomica + backup automatico.

Uso:  venv/bin/python reconstruir_dia22.py
"""
import json
import os
import shutil
from datetime import datetime

BOT_DIR = os.path.dirname(os.path.abspath(__file__))
PICKS_FILE = os.path.join(BOT_DIR, "picks_guardados.json")
COMBINADAS_FILE = os.path.join(BOT_DIR, "combinadas.json")


def _id(*parts):
    base = "-".join(str(p) for p in parts)
    return "REC-" + str(abs(hash(base)) % 10_000_000)


# ─── PREMATCH 22/05 (version 13:46 — 14 picks) ────────────────────────
# (partido, league, country, hora, mercado, jugada, prob, score, riesgo,
#  cuota, estado, resultado)
PREMATCH = [
    ("Machida Zelvia vs Urawa", "J-League", "Japan", "05:30",
     "Goles", "Under 3.5 goles", 90, 10.0, 1.0, 1.23, "acierto", "1-0"),
    ("Juan Pablo II College vs FBC Melgar", "Perú Liga 1", "Peru", "15:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.32, "pendiente", None),
    ("San Antonio Bulo Bulo vs ABB", "Bolivia División Profesional", "Bolivia", "14:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.25, "pendiente", None),
    ("Rot-Weiß Essen vs SpVgg Greuther Fürth", "Bundesliga 2", "Germany", "13:30",
     "Goles", "Over 2.5 goles", 78, 9.2, 2.0, 1.38, "pendiente", None),
    ("Djurgardens IF vs IF Brommapojkarna", "Allsvenskan", "Sweden", "12:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.18, "pendiente", None),
    ("Everton de Vina vs Coquimbo Unido", "Chile Primera División", "Chile", "14:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.51, "pendiente", None),
    ("Liverpool Montevideo vs Racing Montevideo", "Uruguay Primera División", "Uruguay", "17:30",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.60, "pendiente", None),
    ("Liverpool Montevideo vs Racing Montevideo", "Uruguay Primera División", "Uruguay", "17:30",
     "Goles", "Under 3.5 goles", 86, 8.3, 1.0, 1.26, "pendiente", None),
    ("Rot-Weiß Essen vs SpVgg Greuther Fürth", "Bundesliga 2", "Germany", "13:30",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "pendiente", None),
    ("Fiorentina vs Atalanta", "Serie A Italia", "Italy", "13:45",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "pendiente", None),
    ("Independiente del Valle vs Libertad", "Ecuador Liga Pro", "Ecuador", "19:00",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "pendiente", None),
    ("Sudtirol vs Bari", "Serie B Italia", "Italy", "13:00",
     "Doble Oportunidad", "X2", 78, 8.0, 2.8, 1.38, "pendiente", None),
    ("Everton de Vina vs Coquimbo Unido", "Chile Primera División", "Chile", "14:00",
     "Corners", "Corners Over 8.5", 77, 8.0, 3.0, 1.40, "pendiente", None),
    ("Sudtirol vs Bari", "Serie B Italia", "Italy", "13:00",
     "Goles", "Over 1.5 goles", 83, 7.5, 2.8, 1.43, "pendiente", None),
]

# ─── LIVE 22/05 (13:46 — 23 picks) ────────────────────────────────────
# (partido, league, country, hora, minuto, mercado, jugada, prob, score,
#  riesgo, cuota, estado, resultado)
LIVE = [
    ("El Gouna FC vs El Geish", "Premier League", "Egypt", "09:00", 70,
     "Corners", "Corners Over 10.5", 76, 8.0, 2.0, 1.72, "acierto", "11 corners"),
    ("Zeleznicar Pancevo vs Cukaricki", "Super Liga", "Serbia", "10:00", 69,
     "Corners", "Corners Over 9.5", 76, 8.0, 2.0, 1.65, "acierto", "14 corners"),
    ("ML Vitebsk vs FC Gomel", "Premier League", "Belarus", "12:00", 45,
     "Tarjetas", "Tarjetas Over 3.5", 76, 7.6, 3.5, 1.65, "pendiente", None),
    ("NK Osijek vs NK Slaven Belupo", "HNL", "Croatia", "09:00", 30,
     "Goles", "Over 0.5 gol HT Live", 74, 7.5, 4.2, 1.65, "acierto", "2-0"),
    ("El Gouna FC vs El Geish", "Premier League", "Egypt", "09:00", 30,
     "Goles", "Over 0.5 gol HT Live", 74, 7.5, 4.2, 1.65, "acierto", "2-1"),
    ("El Gouna FC vs El Geish", "Premier League", "Egypt", "09:00", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "2-1"),
    ("Ried vs Rapid Vienna", "Bundesliga", "Austria", "12:30", 37,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "pendiente", None),
    ("Pharco vs National Bank of Egypt", "Premier League", "Egypt", "12:00", 72,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "pendiente", None),
    ("Zeleznicar Pancevo vs Cukaricki", "Super Liga", "Serbia", "10:00", 20,
     "Corners", "Corners HT Over 4.5", 74, 7.4, 4.2, 1.65, "acierto", "14 corners"),
    ("HNK Hajduk Split vs Vukovar", "HNL", "Croatia", "11:15", 29,
     "Corners", "Corners HT Over 4.5", 74, 7.4, 4.2, 1.65, "acierto", "11 corners"),
    ("Ried vs Rapid Vienna", "Bundesliga", "Austria", "12:30", 19,
     "Corners", "Corners HT Over 4.5", 74, 7.4, 4.2, 1.65, "pendiente", None),
    ("Ried vs Rapid Vienna", "Bundesliga", "Austria", "12:30", 26,
     "Corners", "Corners HT Over 5.5", 72, 7.2, 4.8, 1.75, "pendiente", None),
    ("NK Osijek vs NK Slaven Belupo", "HNL", "Croatia", "09:00", 45,
     "Corners", "Corners Over 10.5", 76, 7.0, 3.0, 1.75, "acierto", "18 corners"),
    ("Zeleznicar Pancevo vs Cukaricki", "Super Liga", "Serbia", "10:00", 37,
     "Goles", "Over 0.5 gol HT Live", 70, 7.0, 4.8, 1.75, "fallo", "0-0"),
    ("Zeleznicar Pancevo vs Cukaricki", "Super Liga", "Serbia", "10:00", 50,
     "Corners", "Corners Over 8.5", 76, 7.0, 3.0, 1.62, "acierto", "14 corners"),
    ("HNK Hajduk Split vs Vukovar", "HNL", "Croatia", "11:15", 45,
     "Corners", "Corners Over 10.5", 76, 7.0, 3.0, 1.75, "acierto", "11 corners"),
    ("Pharco vs National Bank of Egypt", "Premier League", "Egypt", "12:00", 27,
     "Goles", "Over 0.5 gol HT Live", 70, 7.0, 4.8, 1.75, "pendiente", None),
    ("Djurgardens IF vs IF Brommapojkarna", "Allsvenskan", "Sweden", "12:00", 45,
     "Corners", "Corners Over 9.5", 76, 7.0, 3.0, 1.70, "pendiente", None),
    ("CFR 1907 Cluj vs Arges Pitesti", "Liga I", "Romania", "12:30", 27,
     "Goles", "Over 0.5 gol HT Live", 70, 7.0, 4.8, 1.75, "pendiente", None),
    ("Pharco vs National Bank of Egypt", "Premier League", "Egypt", "12:00", 65,
     "Corners", "Corners Over 9.5", 76, 7.0, 3.0, 1.65, "pendiente", None),
    ("Pharco vs National Bank of Egypt", "Premier League", "Egypt", "12:00", 69,
     "Corners", "Corners Over 10.5", 76, 7.0, 3.0, 1.72, "pendiente", None),
    ("Pharco vs National Bank of Egypt", "Premier League", "Egypt", "12:00", 71,
     "Corners", "Corners Over 11.5", 76, 7.0, 3.0, 1.80, "pendiente", None),
    ("Sudtirol vs Bari", "Serie B Italia", "Italy", "13:00", 37,
     "Goles", "Over 0.5 gol HT Live", 70, 7.0, 4.8, 1.75, "pendiente", None),
]

# ─── COMBINADAS 22/05 (09:56 — 3 combinadas) ──────────────────────────
COMBINADAS = [
    ("2026-05-22", "Triple", "pre", 2.60, "pendiente", "COMB-PRE-260522-4111F4", [
        {"partido": "Machida Zelvia vs Urawa", "jugada": "Under 3.5 goles", "score": 9.2, "riesgo": 1.0, "cuota": 1.23},
        {"partido": "Juan Pablo II College vs FBC Melgar", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.32},
        {"partido": "Liverpool Montevideo vs Racing Montevideo", "jugada": "Over 1.5 goles", "score": 8.3, "riesgo": 2.0, "cuota": 1.60},
    ]),
    ("2026-05-22", "Triple", "pre", 2.85, "pendiente", "COMB-PRE-260522-08FD34", [
        {"partido": "Juan Pablo II College vs FBC Melgar", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.32},
        {"partido": "Everton de Vina vs Coquimbo Unido", "jugada": "Over 1.5 goles", "score": 8.3, "riesgo": 2.0, "cuota": 1.51},
        {"partido": "Sudtirol vs Bari", "jugada": "Over 1.5 goles", "score": 7.5, "riesgo": 2.8, "cuota": 1.43},
    ]),
    ("2026-05-22", "Triple", "pre", 2.51, "pendiente", "COMB-PRE-260522-E9D4C5", [
        {"partido": "Juan Pablo II College vs FBC Melgar", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.32},
        {"partido": "Rot-Weiß Essen vs SpVgg Greuther Fürth", "jugada": "1X", "score": 8.0, "riesgo": 2.8, "cuota": 1.38},
        {"partido": "Fiorentina vs Atalanta", "jugada": "1X", "score": 8.0, "riesgo": 2.8, "cuota": 1.38},
    ]),
]

FECHA = "2026-05-22"


def cargar(path):
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []


def guardar_atomico(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(tmp, path)


def main():
    print("=" * 60)
    print("RECONSTRUCCION DE PICKS — 22 de mayo 2026")
    print("=" * 60)

    picks = cargar(PICKS_FILE)
    combinadas = cargar(COMBINADAS_FILE)
    print(f"Picks actuales:      {len(picks)}")
    print(f"Combinadas actuales: {len(combinadas)}")

    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bkp = os.path.join(BOT_DIR, "backups")
    os.makedirs(bkp, exist_ok=True)
    if os.path.exists(PICKS_FILE):
        shutil.copy(PICKS_FILE, os.path.join(bkp, f"picks_{ts}.json"))
    if os.path.exists(COMBINADAS_FILE):
        shutil.copy(COMBINADAS_FILE, os.path.join(bkp, f"combinadas_{ts}.json"))
    print(f"Backup en backups/ (sufijo {ts})")
    print()

    add_pre = skip_pre = 0
    for (partido, league, country, hora, mercado, jugada,
         prob, score, riesgo, cuota, estado, resultado) in PREMATCH:
        dup = any(p.get("partido") == partido and p.get("jugada") == jugada
                  and (p.get("fecha") == FECHA or p.get("fecha_partido") == FECHA)
                  for p in picks)
        if dup:
            skip_pre += 1
            continue
        picks.append({
            "fixture_id": _id(FECHA, partido, jugada),
            "fecha": FECHA, "fecha_partido": FECHA, "hora": hora,
            "country": country, "league": league, "partido": partido,
            "mercado": mercado, "jugada": jugada,
            "probabilidad": prob, "score": score, "riesgo": riesgo,
            "cuota_minima": cuota, "cuota": cuota,
            "cuota_pinnacle": None, "bookmaker": "",
            "estado": estado, "resultado_real": resultado,
            "tipo": "prematch", "es_seleccion": False,
            "reconstruido": True, "timestamp": f"{FECHA} 13:46:00",
        })
        add_pre += 1

    add_live = skip_live = 0
    for (partido, league, country, hora, minuto, mercado, jugada,
         prob, score, riesgo, cuota, estado, resultado) in LIVE:
        dup = any(p.get("partido") == partido and p.get("jugada") == jugada
                  and (p.get("fecha") == FECHA or p.get("fecha_partido") == FECHA)
                  and p.get("minuto_consulta") == minuto
                  for p in picks)
        if dup:
            skip_live += 1
            continue
        picks.append({
            "fixture_id": _id(FECHA, partido, jugada, minuto),
            "fecha": FECHA, "fecha_partido": FECHA, "hora": hora,
            "country": country, "league": league, "partido": partido,
            "mercado": mercado, "jugada": jugada,
            "probabilidad": prob, "score": score, "riesgo": riesgo,
            "cuota_minima": cuota, "cuota": cuota,
            "cuota_pinnacle": None, "bookmaker": "",
            "estado": estado, "resultado_real": resultado,
            "tipo": "live", "minuto_consulta": minuto,
            "es_seleccion": False, "reconstruido": True,
            "timestamp": f"{FECHA} 13:46:00",
        })
        add_live += 1

    guardar_atomico(PICKS_FILE, picks)

    add_comb = skip_comb = 0
    tickets = {c.get("ticket_id") for c in combinadas}
    for (fecha, tipo, subtipo, cuota_c, estado, ticket, cps) in COMBINADAS:
        if ticket in tickets:
            skip_comb += 1
            continue
        combinadas.append({
            "fecha": fecha, "tipo": tipo, "subtipo": subtipo,
            "cuota_combinada": cuota_c, "estado": estado,
            "ticket_id": ticket, "n_picks": len(cps),
            "picks": cps, "reconstruido": True,
        })
        add_comb += 1

    guardar_atomico(COMBINADAS_FILE, combinadas)

    print("RESULTADO:")
    print(f"  Prematch  — agregados: {add_pre:2d} | ya existian: {skip_pre}")
    print(f"  Live      — agregados: {add_live:2d} | ya existian: {skip_live}")
    print(f"  Combinadas— agregadas: {add_comb:2d} | ya existian: {skip_comb}")
    print()
    print(f"Total picks ahora:      {len(picks)}")
    print(f"Total combinadas ahora: {len(combinadas)}")
    print()
    print("Los picks pendientes se cerraran con /rendimiento o el job auto.")


if __name__ == "__main__":
    main()
