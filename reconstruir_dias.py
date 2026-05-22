"""
reconstruir_dias.py
HarryNine V14 — Reconstruccion de picks perdidos: 19, 20 y 21 de mayo 2026.

Los picks de estos dias se perdieron (bug de persistencia + git reset --hard
sobrescribiendo los .json). Este script los reinserta en picks_guardados.json
a partir de los reportes PDF que el usuario conservaba.

- No duplica: si un pick (fixture/jugada/fecha) ya existe, lo salta.
- Los picks prematch -> tipo "prematch" (origen analizar_all)
- Los picks live    -> tipo "live"     (origen live_all)
- Hace backup automatico antes de escribir.

Uso:  venv/bin/python reconstruir_dias.py
"""
import json
import os
import shutil
from datetime import datetime

# ─── Localizar archivos ───────────────────────────────────────────────
BOT_DIR = os.path.dirname(os.path.abspath(__file__))
PICKS_FILE = os.path.join(BOT_DIR, "picks_guardados.json")
COMBINADAS_FILE = os.path.join(BOT_DIR, "combinadas.json")


def _id(*parts):
    """Genera un fixture_id sintetico estable para picks reconstruidos."""
    base = "-".join(str(p) for p in parts)
    return "REC-" + str(abs(hash(base)) % 10_000_000)


# ─── PICKS PREMATCH ───────────────────────────────────────────────────
# Formato: (fecha, partido, league, country, hora, mercado, jugada,
#           prob, score, riesgo, cuota, estado, resultado_real)
PREMATCH = [
    # ===== 19/05 (RESUMEN PREMATCH 19:05 — todos cerrados) =====
    ("2026-05-19", "Fluminense vs Bolívar", "CONMEBOL Libertadores", "World", "17:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.25, "acierto", "2-1"),
    ("2026-05-19", "A. Italiano vs Barracas Central", "CONMEBOL Sudamericana", "World", "17:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.28, "acierto", "2-0"),
    ("2026-05-19", "Rosario Central vs UCV", "CONMEBOL Libertadores", "World", "17:00",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "acierto", "4-0"),
    ("2026-05-19", "Coquimbo Unido vs Deportes Tolima", "CONMEBOL Libertadores", "World", "17:00",
     "Corners", "Corners Over 8.5", 77, 8.0, 3.0, 1.40, "acierto", "12 corners"),
    ("2026-05-19", "Atletico Torque vs Deportivo Riestra", "CONMEBOL Sudamericana", "World", "17:00",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "acierto", "4-1"),

    # ===== 20/05 (RESUMEN PREMATCH 19:14 — todos cerrados) =====
    ("2026-05-20", "Gais vs Hammarby FF", "Allsvenskan", "Sweden", "12:00",
     "Goles", "Under 3.5 goles", 91, 10.0, 1.0, 1.20, "acierto", "2-0"),
    ("2026-05-20", "Santos vs San Lorenzo", "CONMEBOL Sudamericana", "World", "17:00",
     "Goles", "Under 3.5 goles", 91, 10.0, 1.0, 1.20, "fallo", "2-2"),
    ("2026-05-20", "Palermo vs Catanzaro", "Serie B Italia", "Italy", "13:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.25, "acierto", "2-0"),
    ("2026-05-20", "Aalesund vs Brann", "Eliteserien", "Norway", "13:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.25, "acierto", "2-1"),
    ("2026-05-20", "Start vs Bodo/Glimt", "Eliteserien", "Norway", "11:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.28, "acierto", "1-4"),
    ("2026-05-20", "Lillestrom vs Kristiansund BK", "Eliteserien", "Norway", "12:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.28, "acierto", "1-2"),
    ("2026-05-20", "Club Nacional vs Universitario", "CONMEBOL Libertadores", "World", "17:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.28, "fallo", "0-0"),
    ("2026-05-20", "Boston River vs O'Higgins", "CONMEBOL Sudamericana", "World", "17:00",
     "Goles", "Over 1.5 goles", 85, 8.3, 2.0, 1.28, "acierto", "3-2"),
    ("2026-05-20", "Torreense vs Casa Pia", "Primeira Liga", "Portugal", "12:00",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "acierto", "0-0"),
    ("2026-05-20", "Olimpia vs Vasco DA Gama", "CONMEBOL Sudamericana", "World", "17:00",
     "Doble Oportunidad", "1X", 78, 8.0, 2.8, 1.38, "acierto", "3-1"),

    # ===== 21/05 (RESUMEN PREMATCH 17:44 — mezcla cerrados/pendientes) =====
    ("2026-05-21", "Ajax vs Groningen", "Eredivisie", "Netherlands", "11:45",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.18, "acierto", "2-0"),
    ("2026-05-21", "IF Elfsborg vs Mjallby AIF", "Allsvenskan", "Sweden", "12:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.30, "acierto", "1-1"),
    ("2026-05-21", "Utrecht vs Heerenveen", "Eredivisie", "Netherlands", "14:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.22, "acierto", "3-2"),
    ("2026-05-21", "Deportivo La Guaira vs Independ. Rivadavia", "Copa Libertadores", "World", "17:00",
     "Goles", "Under 3.5 goles", 88, 9.2, 1.0, 1.18, "pendiente", None),
    ("2026-05-21", "Atletico-MG vs Cienciano", "Copa Sudamericana", "World", "17:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.18, "pendiente", None),
    ("2026-05-21", "Puerto Cabello vs Juventud", "Copa Sudamericana", "World", "17:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.37, "pendiente", None),
    ("2026-05-21", "Macara vs Alianza Atletico", "Copa Sudamericana", "World", "21:00",
     "Goles", "Over 1.5 goles", 87, 9.2, 1.1, 1.26, "pendiente", None),
    ("2026-05-21", "VfL Wolfsburg vs SC Paderborn 07", "Bundesliga", "Germany", "13:30",
     "Doble Oportunidad", "X2", 78, 8.0, 2.8, 1.38, "acierto", "0-0"),
    ("2026-05-21", "KV Mechelen vs Club Brugge KV", "Bélgica Pro League", "Belgium", "13:30",
     "Doble Oportunidad", "X2", 78, 8.0, 2.8, 1.38, "acierto", "2-2"),
    ("2026-05-21", "Anderlecht vs St. Truiden", "Bélgica Pro League", "Belgium", "13:30",
     "Corners", "Corners Over 8.5", 77, 8.0, 3.0, 1.47, "acierto", "17 corners"),
    ("2026-05-21", "Racing Club vs Caracas FC", "Copa Sudamericana", "World", "19:00",
     "Doble Oportunidad", "X2", 78, 8.0, 2.8, 1.38, "pendiente", None),
    ("2026-05-21", "Penarol vs Corinthians", "Copa Libertadores", "World", "19:30",
     "Corners", "Corners Over 8.5", 77, 8.0, 3.0, 1.54, "pendiente", None),
    ("2026-05-21", "Gent vs Union St. Gilloise", "Bélgica Pro League", "Belgium", "13:30",
     "Tarjetas", "Tarjetas Over 4.5", 76, 7.8, 3.4, 2.40, "fallo", "4 tarjetas"),
    ("2026-05-21", "U. Catolica vs Barcelona SC", "Copa Libertadores", "World", "19:30",
     "Tarjetas", "Tarjetas Over 4.5", 76, 7.8, 3.4, 1.44, "pendiente", None),
    ("2026-05-21", "Blooming vs Carabobo FC", "Copa Sudamericana", "World", "19:30",
     "Tarjetas", "Tarjetas Over 4.5", 76, 7.8, 3.4, 1.42, "pendiente", None),
]

# ─── PICKS LIVE ───────────────────────────────────────────────────────
# Formato: (fecha, partido, league, country, hora, minuto, mercado, jugada,
#           prob, score, riesgo, cuota, estado, resultado_real)
LIVE = [
    # ===== 19/05 (RESUMEN LIVE 19:04 — 20 picks) =====
    ("2026-05-19", "A. Italiano vs Barracas Central", "CONMEBOL Sudamericana", "World", "17:00", 72,
     "Corners", "Corners Over 11.5", 76, 9.0, 2.0, 1.80, "fallo", "11 corners"),
    ("2026-05-19", "Sichuan Jiuniu vs Dalian Zhixing", "Super League", "China", "06:35", 62,
     "Corners", "Corners Over 11.5", 76, 8.0, 2.0, 1.80, "acierto", "14 corners"),
    ("2026-05-19", "Hapoel Beer Sheva vs Maccabi Tel Aviv", "Ligat Ha'al", "Israel", "12:30", 64,
     "Corners", "Corners Over 11.5", 76, 8.0, 2.0, 1.80, "acierto", "13 corners"),
    ("2026-05-19", "Genk vs Antwerp", "Jupiler Pro League", "Belgium", "13:30", 56,
     "Corners", "Corners Over 11.5", 76, 8.0, 2.0, 1.80, "acierto", "14 corners"),
    ("2026-05-19", "Atletico Torque vs Deportivo Riestra", "CONMEBOL Sudamericana", "World", "17:00", 70,
     "Corners", "Corners Over 11.5", 76, 8.0, 2.0, 1.80, "acierto", "14 corners"),
    ("2026-05-19", "Rouen vs Laval", "Ligue 2", "France", "13:30", 59,
     "Tarjetas", "Tarjetas Over 3.5", 76, 7.6, 3.5, 1.65, "acierto", "6 tarjetas"),
    ("2026-05-19", "Fluminense vs Bolívar", "CONMEBOL Libertadores", "World", "17:00", 45,
     "Tarjetas", "Tarjetas Over 3.5", 76, 7.6, 3.5, 1.65, "acierto", "7 tarjetas"),
    ("2026-05-19", "NorthEast United vs Mohammedan", "Indian Super League", "India", "06:30", 74,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "2-0"),
    ("2026-05-19", "Bournemouth vs Manchester City", "Premier League", "England", "13:30", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "1-1"),
    ("2026-05-19", "Charleroi vs OH Leuven", "Jupiler Pro League", "Belgium", "13:30", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "1-1"),
    ("2026-05-19", "Rouen vs Laval", "Ligue 2", "France", "13:30", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "1-1"),
    ("2026-05-19", "A. Italiano vs Barracas Central", "CONMEBOL Sudamericana", "World", "17:00", 38,
     "Goles", "Over 0.5 gol HT Live", 74, 7.5, 4.2, 1.65, "acierto", "2-0"),
    ("2026-05-19", "Atletico Torque vs Deportivo Riestra", "CONMEBOL Sudamericana", "World", "17:00", 40,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "4-1"),
    ("2026-05-19", "A. Italiano vs Barracas Central", "CONMEBOL Sudamericana", "World", "17:00", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "2-0"),
    ("2026-05-19", "Coquimbo Unido vs Deportes Tolima", "CONMEBOL Libertadores", "World", "17:00", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "3-0"),
    ("2026-05-19", "Rosario Central vs UCV", "CONMEBOL Libertadores", "World", "17:00", 63,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "pendiente", None),
    ("2026-05-19", "Rouen vs Laval", "Ligue 2", "France", "13:30", 23,
     "Corners", "Corners HT Over 4.5", 74, 7.4, 4.2, 1.65, "fallo", "4 corners"),
    ("2026-05-19", "Chelsea vs Tottenham", "Premier League", "England", "14:15", 31,
     "Corners", "Corners HT Over 4.5", 74, 7.4, 4.2, 1.65, "acierto", "7 corners"),
    ("2026-05-19", "Genk vs Antwerp", "Jupiler Pro League", "Belgium", "13:30", 45,
     "Corners", "Corners Over 8.5", 76, 7.0, 3.0, 1.62, "acierto", "14 corners"),
    ("2026-05-19", "Charleroi vs OH Leuven", "Jupiler Pro League", "Belgium", "13:30", 58,
     "Corners", "Corners Over 11.5", 76, 7.0, 3.0, 1.80, "acierto", "19 corners"),

    # ===== 20/05 (RESUMEN LIVE 19:14 — 23 picks, todos cerrados) =====
    ("2026-05-20", "Shanghai Shenhua vs Wuhan Three Towns", "Super League", "China", "06:35", 66,
     "Corners", "Corners Over 9.5", 76, 9.0, 2.0, 1.65, "fallo", "8 corners"),
    ("2026-05-20", "Olimpia vs Vasco DA Gama", "CONMEBOL Sudamericana", "World", "17:00", 72,
     "Corners", "Corners Over 11.5", 76, 9.0, 2.0, 1.80, "acierto", "15 corners"),
    ("2026-05-20", "Boston River vs O'Higgins", "CONMEBOL Sudamericana", "World", "17:00", 90,
     "Corners", "Corners Over 11.5", 76, 9.0, 2.0, 1.70, "fallo", "11 corners"),
    ("2026-05-20", "Club Nacional vs Universitario", "CONMEBOL Libertadores", "World", "17:00", 90,
     "Corners", "Corners Over 11.5", 76, 8.0, 2.0, 1.70, "acierto", "12 corners"),
    ("2026-05-20", "Zamalek SC vs Ceramica Cleopatra", "Premier League", "Egypt", "12:00", 59,
     "Tarjetas", "Tarjetas Over 3.5", 76, 7.6, 3.5, 1.65, "acierto", "6 tarjetas"),
    ("2026-05-20", "Al Najma vs Al Shabab", "Pro League", "Saudi-Arabia", "13:00", 38,
     "Tarjetas", "Tarjetas Over 3.5", 76, 7.6, 3.5, 1.65, "acierto", "8 tarjetas"),
    ("2026-05-20", "Hangzhou Greentown vs Shandong Luneng", "Super League", "China", "07:00", 49,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "4-1"),
    ("2026-05-20", "Rotor Volgograd vs Akron", "Premier League", "Russia", "11:30", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "0-2"),
    ("2026-05-20", "Gais vs Hammarby FF", "Allsvenskan", "Sweden", "12:00", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "2-0"),
    ("2026-05-20", "Zamalek SC vs Ceramica Cleopatra", "Premier League", "Egypt", "12:00", 42,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "1-0"),
    ("2026-05-20", "Torreense vs Casa Pia", "Primeira Liga", "Portugal", "12:00", 42,
     "Goles", "Over 0.5 gol HT Live", 74, 7.5, 4.2, 1.65, "fallo", "0-0"),
    ("2026-05-20", "Lillestrom vs Kristiansund BK", "Eliteserien", "Norway", "12:00", 37,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "1-2"),
    ("2026-05-20", "AL Masry vs Al Ahly", "Premier League", "Egypt", "12:00", 63,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "0-2"),
    ("2026-05-20", "Palermo vs Catanzaro", "Serie B Italia", "Italy", "13:00", 36,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "2-0"),
    ("2026-05-20", "SC Freiburg vs Aston Villa", "UEFA Europa League", "World", "14:00", 90,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "fallo", "0-3"),
    ("2026-05-20", "Santos vs San Lorenzo", "CONMEBOL Sudamericana", "World", "17:00", 70,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "2-2"),
    ("2026-05-20", "Pyramids FC vs Smouha SC", "Premier League", "Egypt", "12:00", 19,
     "Corners", "Corners HT Over 4.5", 74, 7.4, 4.2, 1.65, "acierto", "11 corners"),
    ("2026-05-20", "Al Najma vs Al Shabab", "Pro League", "Saudi-Arabia", "13:00", 23,
     "Corners", "Corners HT Over 5.5", 72, 7.2, 4.8, 1.75, "acierto", "17 corners"),
    ("2026-05-20", "Aalesund vs Brann", "Eliteserien", "Norway", "13:00", 23,
     "Corners", "Corners HT Over 5.5", 72, 7.2, 4.8, 1.75, "acierto", "11 corners"),
    ("2026-05-20", "Pyramids FC vs Smouha SC", "Premier League", "Egypt", "12:00", 65,
     "Corners", "Corners Over 10.5", 76, 7.0, 3.0, 1.72, "acierto", "11 corners"),
    ("2026-05-20", "Torreense vs Casa Pia", "Primeira Liga", "Portugal", "12:00", 63,
     "Corners", "Corners Over 9.5", 76, 7.0, 3.0, 1.65, "fallo", "8 corners"),
    ("2026-05-20", "Club Nacional vs Universitario", "CONMEBOL Libertadores", "World", "17:00", 73,
     "Corners", "Corners Over 10.5", 76, 7.0, 3.0, 1.72, "acierto", "12 corners"),
    ("2026-05-20", "Aalesund vs Brann", "Eliteserien", "Norway", "13:00", 37,
     "BTTS", "Ambos marcan - Sí", 75, 6.0, 4.0, 1.70, "acierto", "2-1"),

    # ===== 21/05 (RESUMEN LIVE 17:44 — 5 picks) =====
    ("2026-05-21", "Atromitos vs Panserraikos", "Super League 1", "Greece", "10:00", 85,
     "BTTS", "Ambos marcan - Sí", 75, 8.0, 4.0, 1.70, "fallo", "6-0"),
    ("2026-05-21", "Panetolikos vs Asteras Tripolis", "Super League 1", "Greece", "11:00", 45,
     "BTTS", "Ambos marcan - Sí", 75, 7.5, 4.0, 1.70, "acierto", "1-2"),
    ("2026-05-21", "Brondby vs FC Copenhagen", "Superliga", "Denmark", "11:30", 30,
     "Goles", "Over 0.5 gol HT Live", 74, 7.5, 4.2, 1.65, "acierto", "1-3"),
    ("2026-05-21", "Jamshedpur vs Odisha", "Indian Super League", "India", "09:00", 51,
     "Corners", "Corners Over 8.5", 76, 7.0, 3.0, 1.62, "acierto", "12 corners"),
    ("2026-05-21", "Kifisia vs Larisa", "Super League 1", "Greece", "11:00", 45,
     "Corners", "Corners Over 8.5", 76, 7.0, 3.0, 1.62, "fallo", "8 corners"),
]

# ─── COMBINADAS ───────────────────────────────────────────────────────
# Formato: (fecha, tipo, subtipo, cuota_combinada, estado, ticket_id, picks[])
COMBINADAS = [
    ("2026-05-19", "Triple", "pre", 2.67, "fallo", "COMB-PRE-260519-938C7A", [
        {"partido": "Rosario Central vs UCV", "jugada": "1X", "score": 8.0, "riesgo": 2.8, "cuota": 1.38},
        {"partido": "Coquimbo Unido vs Deportes Tolima", "jugada": "Corners Over 8.5", "score": 8.0, "riesgo": 3.0, "cuota": 1.40},
        {"partido": "Atletico Torque vs Deportivo Riestra", "jugada": "1X", "score": 8.0, "riesgo": 2.8, "cuota": 1.38},
    ]),
    ("2026-05-21", "Triple", "pre", 4.27, "fallo", "COMB-PRE-260521-06E8AB", [
        {"partido": "IF Elfsborg vs Mjallby AIF", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.30},
        {"partido": "Puerto Cabello vs Juventud", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.37},
        {"partido": "Gent vs Union St. Gilloise", "jugada": "Tarjetas Over 4.5", "score": 7.8, "riesgo": 3.4, "cuota": 2.40},
    ]),
    ("2026-05-21", "Triple", "pre", 2.74, "pendiente", "COMB-PRE-260521-8E9EEA", [
        {"partido": "IF Elfsborg vs Mjallby AIF", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.30},
        {"partido": "Puerto Cabello vs Juventud", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.37},
        {"partido": "Penarol vs Corinthians", "jugada": "Corners Over 8.5", "score": 8.0, "riesgo": 3.0, "cuota": 1.54},
    ]),
    ("2026-05-21", "Triple", "pre", 3.01, "pendiente", "COMB-PRE-260521-7FFF5B", [
        {"partido": "Anderlecht vs St. Truiden", "jugada": "Corners Over 8.5", "score": 8.0, "riesgo": 3.0, "cuota": 1.47},
        {"partido": "U. Catolica vs Barcelona SC", "jugada": "Tarjetas Over 4.5", "score": 7.8, "riesgo": 3.4, "cuota": 1.44},
        {"partido": "Blooming vs Carabobo FC", "jugada": "Tarjetas Over 4.5", "score": 7.8, "riesgo": 3.4, "cuota": 1.42},
    ]),
    ("2026-05-21", "Triple", "pre", 2.61, "pendiente", "COMB-PRE-260521-A04D12", [
        {"partido": "Puerto Cabello vs Juventud", "jugada": "Over 1.5 goles", "score": 9.2, "riesgo": 1.1, "cuota": 1.37},
        {"partido": "VfL Wolfsburg vs SC Paderborn 07", "jugada": "X2", "score": 8.0, "riesgo": 2.8, "cuota": 1.38},
        {"partido": "KV Mechelen vs Club Brugge KV", "jugada": "X2", "score": 8.0, "riesgo": 2.8, "cuota": 1.38},
    ]),
]


def cargar(path):
    if not os.path.exists(path):
        return []
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []


def guardar_atomico(path, data):
    """Escritura atomica: escribe a .tmp y renombra."""
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(tmp, path)


def existe_pick(picks, fecha, partido, jugada):
    for p in picks:
        if (p.get("partido") == partido
                and p.get("jugada") == jugada
                and (p.get("fecha") == fecha or p.get("fecha_partido") == fecha)):
            return True
    return False


def main():
    print("=" * 64)
    print("RECONSTRUCCION DE PICKS — 19, 20, 21 de mayo 2026")
    print("=" * 64)

    picks = cargar(PICKS_FILE)
    combinadas = cargar(COMBINADAS_FILE)
    print(f"Picks actuales en el archivo:      {len(picks)}")
    print(f"Combinadas actuales en el archivo: {len(combinadas)}")

    # Backup
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bkp_dir = os.path.join(BOT_DIR, "backups")
    os.makedirs(bkp_dir, exist_ok=True)
    if os.path.exists(PICKS_FILE):
        shutil.copy(PICKS_FILE, os.path.join(bkp_dir, f"picks_{ts}.json"))
    if os.path.exists(COMBINADAS_FILE):
        shutil.copy(COMBINADAS_FILE, os.path.join(bkp_dir, f"combinadas_{ts}.json"))
    print(f"Backup guardado en: backups/  (sufijo {ts})")
    print()

    # ── Insertar prematch ──
    add_pre = 0
    skip_pre = 0
    for (fecha, partido, league, country, hora, mercado, jugada,
         prob, score, riesgo, cuota, estado, resultado) in PREMATCH:
        if existe_pick(picks, fecha, partido, jugada):
            skip_pre += 1
            continue
        picks.append({
            "fixture_id": _id(fecha, partido, jugada),
            "fecha": fecha, "fecha_partido": fecha, "hora": hora,
            "country": country, "league": league, "partido": partido,
            "mercado": mercado, "jugada": jugada,
            "probabilidad": prob, "score": score, "riesgo": riesgo,
            "cuota_minima": cuota, "cuota": cuota,
            "cuota_pinnacle": None, "bookmaker": "",
            "estado": estado, "resultado_real": resultado,
            "tipo": "prematch", "es_seleccion": False,
            "reconstruido": True,
            "timestamp": f"{fecha} 12:00:00",
        })
        add_pre += 1

    # ── Insertar live ──
    add_live = 0
    skip_live = 0
    for (fecha, partido, league, country, hora, minuto, mercado, jugada,
         prob, score, riesgo, cuota, estado, resultado) in LIVE:
        # En live el mismo partido+jugada puede repetirse en distinto minuto
        dup = False
        for p in picks:
            if (p.get("partido") == partido and p.get("jugada") == jugada
                    and (p.get("fecha") == fecha or p.get("fecha_partido") == fecha)
                    and p.get("minuto_consulta") == minuto):
                dup = True
                break
        if dup:
            skip_live += 1
            continue
        picks.append({
            "fixture_id": _id(fecha, partido, jugada, minuto),
            "fecha": fecha, "fecha_partido": fecha, "hora": hora,
            "country": country, "league": league, "partido": partido,
            "mercado": mercado, "jugada": jugada,
            "probabilidad": prob, "score": score, "riesgo": riesgo,
            "cuota_minima": cuota, "cuota": cuota,
            "cuota_pinnacle": None, "bookmaker": "",
            "estado": estado, "resultado_real": resultado,
            "tipo": "live", "minuto_consulta": minuto,
            "es_seleccion": False, "reconstruido": True,
            "timestamp": f"{fecha} 15:00:00",
        })
        add_live += 1

    guardar_atomico(PICKS_FILE, picks)

    # ── Insertar combinadas ──
    add_comb = 0
    skip_comb = 0
    tickets_existentes = {c.get("ticket_id") for c in combinadas}
    for (fecha, tipo, subtipo, cuota_comb, estado, ticket_id, comb_picks) in COMBINADAS:
        if ticket_id in tickets_existentes:
            skip_comb += 1
            continue
        combinadas.append({
            "fecha": fecha, "tipo": tipo, "subtipo": subtipo,
            "cuota_combinada": cuota_comb, "estado": estado,
            "ticket_id": ticket_id, "n_picks": len(comb_picks),
            "picks": comb_picks, "reconstruido": True,
        })
        add_comb += 1

    guardar_atomico(COMBINADAS_FILE, combinadas)

    # ── Resumen ──
    print("RESULTADO:")
    print(f"  Prematch  — agregados: {add_pre:3d}  | ya existian: {skip_pre}")
    print(f"  Live      — agregados: {add_live:3d}  | ya existian: {skip_live}")
    print(f"  Combinadas— agregadas: {add_comb:3d}  | ya existian: {skip_comb}")
    print()
    print(f"Total picks ahora:      {len(picks)}")
    print(f"Total combinadas ahora: {len(combinadas)}")
    print()
    print("Picks pendientes quedaran con estado 'pendiente'.")
    print("El job automatico del bot los cerrara consultando la API,")
    print("o puedes forzarlo con /rendimiento (llama a actualizar_resultados).")


if __name__ == "__main__":
    main()
