from telegram import Update
from telegram.ext import ApplicationBuilder, CommandHandler, ContextTypes
from dotenv import load_dotenv
from datetime import datetime, timedelta, time as dtime
from reportlab.lib.pagesizes import A4, landscape
from reportlab.pdfgen import canvas
from reportlab.lib import colors
from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
from reportlab.lib.styles import getSampleStyleSheet
import requests
import os
import json
import time
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np


load_dotenv()

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN")
API_FOOTBALL_KEY = os.getenv("API_FOOTBALL_KEY")

BASE_URL = "https://v3.football.api-sports.io"
HEADERS = {"x-apisports-key": API_FOOTBALL_KEY}

import os as _os_bot
import sys as _sys_bot

def _get_bot_dir():
    """Obtiene el directorio del bot de forma robusta en Windows y Linux."""
    try:
        # Primero intentar __file__
        d = _os_bot.path.dirname(_os_bot.path.abspath(__file__))
        if d and _os_bot.path.isdir(d):
            return d
    except Exception:
        pass
    try:
        # Fallback: directorio del script principal
        d = _os_bot.path.dirname(_os_bot.path.abspath(_sys_bot.argv[0]))
        if d and _os_bot.path.isdir(d):
            return d
    except Exception:
        pass
    # Ultimo recurso: directorio de trabajo actual
    return _os_bot.getcwd()

BOT_DIR = _get_bot_dir()

def _tmp_path(filename):
    """Genera path absoluto para archivos temporales en el directorio del bot."""
    return _os_bot.path.join(BOT_DIR, filename)

PICKS_FILE = _tmp_path("picks_guardados.json")
FEEDBACK_FILE = _tmp_path("feedback.json")
ODDS_HISTORY_FILE = _tmp_path("odds_movimientos.json")
COMBINADAS_FILE = _tmp_path("combinadas.json")
APRENDIZAJE_FILE = _tmp_path("aprendizaje.json")
ESCALERA_FILE = _tmp_path("escalera.json")
BANK_ACUMULADO_FILE = _tmp_path("bank_acumulado.json")
# Suscriptores a alertas live. Un solo job global atiende a todos: asi el
# consumo de API es constante con 1 o con 30 usuarios suscritos.
ALERTAS_SUBS_FILE = _tmp_path("alertas_suscriptores.json")

CACHE = {}
CACHE_TTL = 300
ALERTED_LIVE = set()

EUROPA_LEAGUES = {
    "Premier League": {"id": 39, "season": 2025, "country": "England"},
    "Championship": {"id": 40, "season": 2025, "country": "England"},
    "Bundesliga": {"id": 78, "season": 2025, "country": "Germany"},
    "Bundesliga 2": {"id": 79, "season": 2025, "country": "Germany"}, 
    "Serie A Italia": {"id": 135, "season": 2025, "country": "Italy"},
    "Serie B Italia": {"id": 136, "season": 2025, "country": "Italy"},
    "LaLiga": {"id": 140, "season": 2025, "country": "Spain"},
    "Segunda España": {"id": 141, "season": 2025, "country": "Spain"},
    "Ligue 1": {"id": 61, "season": 2025, "country": "France"},
    "Ligue 2": {"id": 62, "season": 2025, "country": "France"}, 
    "Eredivisie": {"id": 88, "season": 2025, "country": "Netherlands"},
    "Eliteserien": {"id": 103, "season": 2026, "country": "Norway"},
    "Bélgica Pro League": {"id": 144, "season": 2025, "country": "Belgium"},
    "Süper Lig": {"id": 203, "season": 2025, "country": "Turkey"},
    "Primeira Liga": {"id": 94, "season": 2025, "country": "Portugal"},
    "Allsvenskan": {"id": 113, "season": 2026, "country": "Sweden"},
}

SUDAMERICA_LEAGUES = {
    "Argentina Liga Profesional": {"id": 128, "season": 2026, "country": "Argentina"},
    "Brasil Serie A": {"id": 71, "season": 2026, "country": "Brazil"},
    "Copa do Brasil": {"id": 73, "season": 2026, "country": "Brazil"},
    "Perú Liga 1": {"id": 281, "season": 2026, "country": "Peru"},
    "Chile Primera División": {"id": 265, "season": 2026, "country": "Chile"},
    "Colombia Primera A": {"id": 239, "season": 2026, "country": "Colombia"},
    "Uruguay Primera División": {"id": 268, "season": 2026, "country": "Uruguay"},
    "Paraguay Primera División": {"id": 284, "season": 2026, "country": "Paraguay"},
    "Ecuador Liga Pro": {"id": 242, "season": 2026, "country": "Ecuador"},
    "Bolivia División Profesional": {"id": 344, "season": 2026, "country": "Bolivia"},
    "Venezuela Primera División": {"id": 288, "season": 2026, "country": "Venezuela"},
    "Copa Libertadores": {"id": 13, "season": 2026, "country": "World"},
    "Copa Sudamericana": {"id": 11, "season": 2026, "country": "World"},
}

OTRAS_LEAGUES = {
    "MLS": {"id": 253, "season": 2026, "country": "USA"},
    "J-League": {"id": 98, "season": 2026, "country": "Japan"},
}


# ══════════════════════════════════════════════════════════════════════
# RECALIBRACION V14 — capa de correccion basada en datos reales
# (279-491 picks cerrados, periodo 16-23 mayo 2026).
# El motor de scoring usa reglas fijas; estas funciones corrigen score y
# probabilidad para que reflejen la efectividad REAL medida, no la teorica.
# ══════════════════════════════════════════════════════════════════════

# Cuota minima exigida a cualquier pick individual. Por debajo de esto el
# pick no es rentable aunque acierte: 80% de acierto necesita >=1.25 solo
# para break-even; 1.50 da colchon ante error de calibracion.
CUOTA_MINIMA_PICK = 1.50

# Cuota minima de cada eslabon dentro de una combinada (coherente con el
# filtro de picks individuales).
CUOTA_MINIMA_ESLABON = 1.50

# Rango de cuota total aceptable para una combinada.
CUOTA_COMBINADA_MIN = 2.50
CUOTA_COMBINADA_MAX = 4.50

# Umbrales minimos por eslabon de combinada (sobre valores recalibrados).
COMB_PROB_MIN = 80.0
COMB_SCORE_MIN = 7.5
# Over 1.5 es el eslabon que mas rompe combinadas (0-0 / 1-0). Se le exige
# un score recalibrado mas alto que al resto.
COMB_SCORE_MIN_OVER15 = 8.0

# Multiplicador de score por liga. Medido sobre efectividad real por liga.
# Ligas con muestra < 10 picks quedan neutras (1.00) por falta de datos.
MULTIPLICADOR_LIGA = {
    "Premier League": 1.05,   # 87.9% (n=33)
    "La Liga": 0.70,          # 42.1% (n=19)
    "LaLiga": 0.70,           # alias del mismo torneo
    "Süper Lig": 0.80,        # 50.0% (n=12)
    "Super Lig": 0.80,        # alias sin diacritico
    "2. Bundesliga": 0.88,    # 63.2% (n=19)
    "Bundesliga 2": 0.88,     # alias
    "Ligue 1": 0.88,          # 63.2% (n=19)
    "Serie A": 0.92,          # 67.7% (n=31)
    "Serie A Italia": 0.92,   # alias
}


def recalibrar_probabilidad(prob):
    """
    Corrige la probabilidad declarada hacia la efectividad real medida.
    La banda 75-79% concentraba el 64% de los picks y rendia solo 62%.
    """
    try:
        prob = float(prob)
    except (ValueError, TypeError):
        return prob
    if prob >= 90:
        return 94.0
    if prob >= 85:
        return 88.0
    if prob >= 80:
        return 78.0          # tramo interpolado (sin datos directos)
    if prob >= 75:
        return 62.0          # banda peor calibrada: -14 pp reales
    if prob >= 70:
        return 88.0          # banda 70-74 rinde 91% real
    return prob


def recalibrar_score(score):
    """
    Re-mapea el score a la efectividad real. El score original no ordena
    (7.0-7.4 rinde mas que 8.0-8.4); esta tabla lo corrige.
    """
    try:
        score = float(score)
    except (ValueError, TypeError):
        return score
    if score >= 9.5:
        return 9.0
    if score >= 9.0:
        return 7.5
    if score >= 8.5:
        return 7.2           # tramo sin datos: interpolado conservador
    if score >= 8.0:
        return 6.8
    if score >= 7.5:
        return 6.7
    if score >= 7.0:
        return 8.5           # tramo 7.0-7.4 rinde 85% real
    return 5.0


def multiplicador_liga(liga):
    """Retorna el factor de ajuste de score para una liga dada."""
    if not liga:
        return 1.0
    return MULTIPLICADOR_LIGA.get(liga, 1.0)


def aplicar_recalibracion(rec, liga=None):
    """
    Aplica la recalibracion completa a una recomendacion (dict con claves
    prob/score). Guarda los valores originales y deja los recalibrados como
    los oficiales. Idempotente: si ya fue recalibrada, no la altera.
    """
    if not rec or rec.get("_recalibrado"):
        return rec

    prob_orig = rec.get("prob", rec.get("probabilidad"))
    score_orig = rec.get("score")

    if prob_orig is not None:
        prob_nueva = recalibrar_probabilidad(prob_orig)
        rec["prob_original"] = prob_orig
        rec["prob"] = prob_nueva
        if "probabilidad" in rec:
            rec["probabilidad"] = prob_nueva

    if score_orig is not None:
        score_nuevo = recalibrar_score(score_orig)
        score_nuevo = round(score_nuevo * multiplicador_liga(liga), 1)
        score_nuevo = clamp(score_nuevo, 0, 10)
        rec["score_original"] = score_orig
        rec["score"] = score_nuevo
        # La etiqueta de confianza debe reflejar el score recalibrado.
        if "confianza" in rec:
            rec["confianza"] = etiqueta_confianza(score_nuevo)

    # La cuota minima teorica depende de la probabilidad: si la prob
    # cambio al recalibrar, se recalcula para que sea coherente.
    if rec.get("prob") is not None and rec.get("riesgo") is not None:
        nueva_cm = cuota_minima(rec["prob"], rec["riesgo"])
        if nueva_cm:
            rec["cuota_minima"] = nueva_cm

    rec["_recalibrado"] = True
    return rec


def umbral_prob_desde_score_legado(score_minimo):
    """
    Traduce los umbrales de score que el codigo usaba antes de la
    recalibracion (7.5 = top normal, 9 = elite/anclas) a umbrales de
    PROBABILIDAD recalibrada. Tras la recalibracion el score cambio de
    rango y un corte fijo de score descartaria casi todo; el criterio
    unico del sistema es ahora la probabilidad recalibrada.
      score_minimo >= 9  -> elite  -> prob recalibrada >= 85%
      score_minimo  < 9  -> normal -> prob recalibrada >= 70%
    """
    try:
        return 85.0 if float(score_minimo) >= 9 else 70.0
    except (ValueError, TypeError):
        return 70.0


def cuota_pick_suficiente(rec):
    """
    True si el pick supera la cuota minima. Usa la mejor cuota disponible
    (API/Pinnacle si existe, si no la cuota minima calculada).
    Si no hay ninguna cuota, se rechaza por prudencia.
    """
    cuota = (rec.get("cuota_api")
             or rec.get("cuota")
             or rec.get("cuota_minima")
             or 0)
    try:
        cuota = float(cuota)
    except (ValueError, TypeError):
        return False
    return cuota >= CUOTA_MINIMA_PICK


def api_get(endpoint, use_cache=True, ttl=CACHE_TTL):
    now = time.time()

    if use_cache and endpoint in CACHE:
        saved_time, saved_data = CACHE[endpoint]
        if now - saved_time < ttl:
            return saved_data

    try:
        r = requests.get(
            f"{BASE_URL}{endpoint}",
            headers=HEADERS,
            timeout=12
        )

        if r.status_code != 200:
            print(f"ERROR API {r.status_code}: {endpoint}")
            return []

        data = r.json().get("response", [])

        if use_cache:
            CACHE[endpoint] = (now, data)

        return data

    except Exception as e:
        print("ERROR REQUEST:", e)
        return []


async def api_get_async(session, endpoint, use_cache=True, ttl=CACHE_TTL):
    """Version asincrona de api_get para llamadas paralelas."""
    import aiohttp as _aiohttp
    now = time.time()

    if use_cache and endpoint in CACHE:
        saved_time, saved_data = CACHE[endpoint]
        if now - saved_time < ttl:
            return saved_data

    try:
        async with session.get(
            f"{BASE_URL}{endpoint}",
            headers=HEADERS,
            timeout=_aiohttp.ClientTimeout(total=12)
        ) as r:
            if r.status != 200:
                return []
            data = (await r.json()).get("response", [])
            if use_cache:
                CACHE[endpoint] = (now, data)
            return data
    except Exception:
        return []


async def _analizar_fixture_async(session, fixture_id, incluir_odds=True):
    """Analiza un fixture de forma asincrona."""
    try:
        # Llamadas paralelas: fixture + odds + forma equipos
        tasks = [
            api_get_async(session, f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600),
        ]
        if incluir_odds:
            tasks.append(api_get_async(session, f"/odds?fixture={fixture_id}", use_cache=True, ttl=600))

        results = await asyncio.gather(*tasks, return_exceptions=True)
        fixture_data = results[0] if not isinstance(results[0], Exception) else []

        if not fixture_data:
            return None

        # Usar datos del fixture para analisis sincrono
        # (las funciones de scoring son sincronas, solo la red es async)
        return preparar_analisis(fixture_id, incluir_odds=incluir_odds)
    except Exception:
        return None


async def _analizar_live_async(session, fixture_id):
    """Analiza un fixture live de forma asincrona."""
    try:
        tasks = [
            api_get_async(session, f"/fixtures/statistics?fixture={fixture_id}", use_cache=False),
        ]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        # Guardar en cache para que analizar_live_fixture los use
        stats = results[0] if not isinstance(results[0], Exception) else []
        if stats:
            CACHE[f"/fixtures/statistics?fixture={fixture_id}"] = (time.time(), stats)
        return analizar_live_fixture(fixture_id)
    except Exception:
        return None


def leer_json(path):
    if not os.path.exists(path):
        return []

    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []


def guardar_json_lista(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def agregar_json(path, item):
    data = leer_json(path)
    data.append(item)
    guardar_json_lista(path, data)


def fecha_peru_obj():
    from datetime import timezone, timedelta as _td
    return datetime.now(timezone.utc).replace(tzinfo=None) - _td(hours=5)


def fecha_hoy_peru():
    return fecha_peru_obj().strftime("%Y-%m-%d")

def fecha_manana_peru():
    return (fecha_peru_obj() + timedelta(days=1)).strftime("%Y-%m-%d")

def fecha_ayer_peru():
    return (fecha_peru_obj() - timedelta(days=1)).strftime("%Y-%m-%d")

def fecha_hora_peru():
    return fecha_peru_obj().strftime("%Y-%m-%d %H:%M:%S")

def obtener_bandera(country):
    banderas = {
        "Spain": "🇪🇸",
        "Brazil": "🇧🇷",
        "Argentina": "🇦🇷",
        "Peru": "🌐",
        "Ecuador": "🇪🇨",
        "Uruguay": "🇺🇾",
        "Colombia": "🇨🇴",
        "Chile": "🇨🇱",
        "Mexico": "🇲🇽",
        "Italy": "🇮🇹",
        "France": "🇫🇷",
        "Germany": "🇩🇪",
        "England": "🏴",
        "Netherlands": "🇳🇱",
        "Belgium": "🇧🇪",
        "Portugal": "🇵🇹",
        "Turkey": "🇹🇷",
        "USA": "🇺🇸",
        "Bolivia": "🇧🇴",
        "Paraguay": "🇵🇾",
        "Venezuela": "🇻🇪",
        "Japan": "🇯🇵",
        "South Korea": "🇰🇷",
        "Saudi Arabia": "🇸🇦",
        "Sweden": "🇸🇪",
        "Norway": "🇳🇴",
        "Denmark": "🇩🇰",
        "Finland": "🇫🇮",
        "Austria": "🇦🇹",
        "Switzerland": "🇨🇭",
        "Poland": "🇵🇱",
        "Croatia": "🇭🇷",
        "Serbia": "🇷🇸",
        "Romania": "🇷🇴",
        "Hungary": "🇭🇺",
        "Czech-Republic": "🇨🇿",
        "Slovakia": "🇸🇰"
    }

    return banderas.get(country, "🌍")

def hora_peru(fecha_api):
    """Convierte fecha UTC de la API a hora Peru (UTC-5)."""
    try:
        from datetime import timezone, timedelta
        dt = datetime.fromisoformat(
            fecha_api.replace("Z", "+00:00")
        )
        # Convertir a UTC-5 (Peru)
        peru_tz = timezone(timedelta(hours=-5))
        dt_peru = dt.astimezone(peru_tz)
        return dt_peru.strftime("%H:%M")
    except Exception:
        try:
            # Fallback: restar 5 horas manualmente
            hora_str = fecha_api[11:16]
            h, m = int(hora_str[:2]), int(hora_str[3:5])
            h = (h - 5) % 24
            return f"{h:02d}:{m:02d}"
        except Exception:
            return fecha_api[11:16]


def clamp(valor, minimo, maximo):
    return max(minimo, min(maximo, valor))


def cuota_justa(probabilidad):
    if probabilidad <= 0:
        return None
    return round(100 / probabilidad, 2)


def cuota_minima(probabilidad, riesgo):
    justa = cuota_justa(probabilidad)

    if not justa:
        return None

    if riesgo <= 3:
        margen = 0.10
    elif riesgo <= 5:
        margen = 0.15
    else:
        margen = 0.22

    return round(justa + margen, 2)


def edge_estimado(probabilidad, cuota_real):
    """
    Calcula el edge (valor esperado) de un pick vs Pinnacle.
    Edge positivo = el mercado nos paga mas de lo que deberia.
    Edge negativo = sin valor, Pinnacle sabe algo que el modelo no.
    """
    if not cuota_real or cuota_real <= 1.0:
        return None
    prob_implicita = 100 / cuota_real
    return round(probabilidad - prob_implicita, 1)


def clasificar_edge(edge):
    """Clasifica el edge en categorias para el usuario."""
    if edge is None:
        return None, "Sin cuota Pinnacle"
    if edge >= 10:
        return "EXCELENTE", f"+{edge}% valor"
    elif edge >= 5:
        return "BUENO", f"+{edge}% valor"
    elif edge >= 2:
        return "LEVE", f"+{edge}% valor"
    elif edge >= 0:
        return "NEUTRO", f"+{edge}% valor"
    else:
        return "SIN VALOR", f"{edge}% (evitar)"


def valor_esperado(probabilidad, cuota_real, stake=1.0):
    """
    Calcula el valor esperado monetario de una apuesta.
    VE > 0 = apuesta con valor positivo
    VE = prob * ganancia - (1-prob) * stake
    """
    if not cuota_real or cuota_real <= 1.0:
        return None
    prob = probabilidad / 100
    ganancia = stake * (cuota_real - 1)
    perdida = stake
    ve = round(prob * ganancia - (1 - prob) * perdida, 4)
    return ve


def score_a_10(score_bruto):
    return round(clamp(score_bruto, 0, 12) / 12 * 10, 1)


def riesgo_a_10(score_10, jugada):
    riesgo = 10 - score_10

    if "Under 3.5" in jugada:
        riesgo -= 1.0

    if "Over 2.5" in jugada or "Ambos marcan" in jugada:
        riesgo += 1.2

    if "Over 1.5" in jugada:
        riesgo += 0.3

    return round(clamp(riesgo, 1, 10), 1)


def etiqueta_confianza(score_10):
    if score_10 >= 9:
        return "🟢 ÉLITE"
    if score_10 >= 8:
        return "🟢 FUERTE"
    if score_10 >= 7:
        return "🟡 ACEPTABLE"
    if score_10 >= 6:
        return "🟠 REGULAR"
    return "🔴 EVITAR"


def porcentaje(v):
    return f"{round(v * 100)}%"


def mercado_categoria(jugada):
    # El orden importa: "Tarjetas Over 3.5" contiene "Over", asi que
    # Tarjetas y Corners deben evaluarse ANTES que Over/Under.
    if "Corners" in jugada:
        return "Corners"
    if "Tarjeta" in jugada:
        return "Tarjetas"
    if "Ambos marcan" in jugada:
        return "Ambos marcan"
    if "1X" in jugada or "X2" in jugada:
        return "Doble oportunidad"
    if "Over" in jugada or "Under" in jugada:
        return "Goles totales"
    return "Otro"

def calcular_forma(team_id, modo=None, last=10):
    partidos = api_get(f"/fixtures?team={team_id}&last={last}")

    jugados = 0
    gf_total = 0
    gc_total = 0
    over15 = 0
    over25 = 0
    under35 = 0
    btts = 0
    forma = []

    for p in partidos:
        gh = p["goals"]["home"]
        ga = p["goals"]["away"]

        if gh is None or ga is None:
            continue

        home_id = p["teams"]["home"]["id"]
        away_id = p["teams"]["away"]["id"]

        if modo == "home" and team_id != home_id:
            continue

        if modo == "away" and team_id != away_id:
            continue

        if team_id == home_id:
            gf, gc = gh, ga
        elif team_id == away_id:
            gf, gc = ga, gh
        else:
            continue

        total = gh + ga

        jugados += 1
        gf_total += gf
        gc_total += gc

        if gf > gc:
            forma.append("W")
        elif gf == gc:
            forma.append("D")
        else:
            forma.append("L")

        if total >= 2:
            over15 += 1
        if total >= 3:
            over25 += 1
        if total <= 3:
            under35 += 1
        if gh > 0 and ga > 0:
            btts += 1

        if jugados == 7:
            break

    if jugados == 0:
        return None

    return {
        "jugados": jugados,
        "gf_prom": gf_total / jugados,
        "gc_prom": gc_total / jugados,
        "total_prom": (gf_total + gc_total) / jugados,
        "over15": over15 / jugados,
        "over25": over25 / jugados,
        "under35": under35 / jugados,
        "btts": btts / jugados,
        "forma": "".join(forma)
    }


def bloque_stats(titulo, stats):
    if not stats:
        return f"{titulo}\nSin datos suficientes.\n"

    return (
        f"{titulo}\n"
        f"Partidos: {stats['jugados']}\n"
        f"Forma: {stats['forma']}\n"
        f"GF prom: {stats['gf_prom']:.2f}\n"
        f"GC prom: {stats['gc_prom']:.2f}\n"
        f"Over 1.5: {porcentaje(stats['over15'])}\n"
        f"Over 2.5: {porcentaje(stats['over25'])}\n"
        f"Under 3.5: {porcentaje(stats['under35'])}\n"
        f"BTTS: {porcentaje(stats['btts'])}\n"
    )


def obtener_recomendaciones(home_general, away_general, home_home, away_away):
    base_home = home_home or home_general
    base_away = away_away or away_general

    if not base_home or not base_away:
        return []

    over15 = (base_home["over15"] + base_away["over15"]) / 2
    over25 = (base_home["over25"] + base_away["over25"]) / 2
    under35 = (base_home["under35"] + base_away["under35"]) / 2
    btts = (base_home["btts"] + base_away["btts"]) / 2
    total_prom = (base_home["total_prom"] + base_away["total_prom"]) / 2

    recomendaciones = []

    def add_pick(jugada, prob, motivo, score_bruto):
        score_10 = score_a_10(score_bruto)
        riesgo_10 = riesgo_a_10(score_10, jugada)

        recomendaciones.append({
            "mercado": mercado_categoria(jugada),
            "jugada": jugada,
            "prob": prob,
            "score": score_10,
            "riesgo": riesgo_10,
            "confianza": etiqueta_confianza(score_10),
            "motivo": motivo,
            "cuota_justa": cuota_justa(prob),
            "cuota_minima": cuota_minima(prob, riesgo_10),
        })

    score_under = 0

    if under35 >= 0.90:
        score_under += 5
    elif under35 >= 0.80:
        score_under += 4
    elif under35 >= 0.75:
        score_under += 3

    if total_prom <= 2.2:
        score_under += 4
    elif total_prom <= 2.6:
        score_under += 3
    elif total_prom <= 2.9:
        score_under += 2

    if btts <= 0.40:
        score_under += 2

    if over25 <= 0.40:
        score_under += 2

    if score_under >= 7:
        prob = min(91, 66 + score_under * 2)
        add_pick(
            "Under 3.5 goles",
            prob,
            "Tendencia under fuerte, bajo promedio goleador y baja frecuencia de partidos rotos.",
            score_under
        )

    score_over15 = 0

    if over15 >= 0.90:
        score_over15 += 5
    elif over15 >= 0.80:
        score_over15 += 4
    elif over15 >= 0.75:
        score_over15 += 3

    if total_prom >= 2.6:
        score_over15 += 4
    elif total_prom >= 2.2:
        score_over15 += 3

    if base_home["gf_prom"] >= 1.2 or base_away["gf_prom"] >= 1.2:
        score_over15 += 2

    if score_over15 >= 7:
        prob = min(90, 65 + score_over15 * 2)
        add_pick(
            "Over 1.5 goles",
            prob,
            "Alta frecuencia de partidos con mínimo 2 goles y producción ofensiva suficiente.",
            score_over15
        )

    score_over25 = 0

    if over25 >= 0.70:
        score_over25 += 5
    elif over25 >= 0.60:
        score_over25 += 4

    if total_prom >= 3.0:
        score_over25 += 4
    elif total_prom >= 2.7:
        score_over25 += 3

    if btts >= 0.65:
        score_over25 += 2

    if score_over25 >= 7:
        prob = min(83, 56 + score_over25 * 2)
        add_pick(
            "Over 2.5 goles",
            prob,
            "Promedio goleador alto, tendencia ofensiva y señales de partido abierto.",
            score_over25
        )

    # BTTS (Ambos marcan) ELIMINADO de la generacion: efectividad real
    # 41.6% (101 picks). La variable `btts` se conserva mas arriba porque
    # alimenta los scores de Under y Over 2.5; solo se elimina la emision
    # del pick. BTTS tambien sigue excluido de combinadas y alertas.

    recomendaciones.sort(key=lambda x: (x["score"], x["prob"]), reverse=True)
    return recomendaciones


def guardar_snapshot_odds(fixture_id, jugada, cuota):
    if not cuota:
        return None

    snapshots = leer_json(ODDS_HISTORY_FILE)

    previos = [
        x for x in snapshots
        if str(x.get("fixture_id")) == str(fixture_id)
        and x.get("jugada") == jugada
    ]

    movimiento = None

    if previos:
        cuota_anterior = previos[-1].get("cuota")
        if cuota_anterior:
            cambio = round(cuota - cuota_anterior, 2)
            if cambio > 0:
                movimiento = f"subió {cambio}"
            elif cambio < 0:
                movimiento = f"bajó {abs(cambio)}"
            else:
                movimiento = "sin cambio"

    snapshots.append({
        "fixture_id": str(fixture_id),
        "jugada": jugada,
        "cuota": cuota,
        "fecha": fecha_hora_peru()
    })

    guardar_json_lista(ODDS_HISTORY_FILE, snapshots)
    return movimiento


def _extraer_cuotas_1x2_pinnacle(odds):
    """
    Extrae las cuotas de Home, Draw, Away del mercado 1X2 de Pinnacle.
    Devuelve dict {"Home": float, "Draw": float, "Away": float} o {} si no hay.
    Usado para calcular Doble Oportunidad desde Pinnacle (que no tiene ese mercado).
    """
    PINNACLE_NAMES = {"Pinnacle", "Pinnacle Sports"}
    WINNER_MARKETS = {"Match Winner", "1X2", "Match Result", "Full Time Result", "Home/Away"}
    resultado = {}
    for casa in odds:
        for book in casa.get("bookmakers", []):
            if book.get("name", "") not in PINNACLE_NAMES:
                continue
            for bet in book.get("bets", []):
                if not any(m.lower() in bet.get("name", "").lower() for m in WINNER_MARKETS):
                    continue
                for value in bet.get("values", []):
                    nombre = str(value.get("value", "")).strip()
                    try:
                        odd = float(value.get("odd"))
                    except Exception:
                        continue
                    if nombre in ("Home", "1", "Home Team"):
                        resultado["Home"] = odd
                    elif nombre in ("Draw", "X", "Tie"):
                        resultado["Draw"] = odd
                    elif nombre in ("Away", "2", "Away Team"):
                        resultado["Away"] = odd
            if resultado:
                return resultado
    return resultado


def _cuota_doble_oportunidad_pinnacle(odds, jugada):
    """
    Calcula la cuota equivalente de Doble Oportunidad desde el 1X2 de Pinnacle.
    Pinnacle no ofrece mercado de Doble Oportunidad directamente.
    Formula: cuota_DC = 1 / (1/cuota_A + 1/cuota_B)
    Devuelve (cuota, "Pinnacle (calc DC)") o (None, None).
    """
    cuotas = _extraer_cuotas_1x2_pinnacle(odds)
    if not cuotas:
        return None, None
    try:
        if jugada == "1X":
            if "Home" in cuotas and "Draw" in cuotas:
                prob = (1 / cuotas["Home"]) + (1 / cuotas["Draw"])
                return round(1 / prob, 3), "Pinnacle (DC calc)"
        elif jugada == "X2":
            if "Draw" in cuotas and "Away" in cuotas:
                prob = (1 / cuotas["Draw"]) + (1 / cuotas["Away"])
                return round(1 / prob, 3), "Pinnacle (DC calc)"
        elif jugada == "12":
            if "Home" in cuotas and "Away" in cuotas:
                prob = (1 / cuotas["Home"]) + (1 / cuotas["Away"])
                return round(1 / prob, 3), "Pinnacle (DC calc)"
    except Exception:
        pass
    return None, None


def _normalizar_jugada_para_matching(jugada):
    """
    Normaliza el texto de la jugada para el matching de cuotas.
    Elimina sufijos de contexto que no forman parte del nombre del mercado:
    ' live', ' restante', ' HT', ' HT Live', ' Live', etc.
    Devuelve la jugada normalizada en lowercase para comparacion.
    """
    import re as _re_norm
    jugada_norm = jugada.strip()
    # Quitar sufijos contextuales (orden importa: mas especifico primero)
    sufijos = [
        r"\s+ht\s+live$", r"\s+ht$", r"\s+live$", r"\s+restante$",
        r"\s+1t$", r"\s+2t$", r"\s+primer\s+tiempo$", r"\s+segundo\s+tiempo$",
    ]
    for suf in sufijos:
        jugada_norm = _re_norm.sub(suf, "", jugada_norm, flags=_re_norm.IGNORECASE).strip()
    return jugada_norm


def buscar_cuota_live(fixture_id, jugada):
    """
    PUNTO 5: Busca la cuota REAL EN VIVO de una jugada usando el endpoint
    /odds/live de api-sports. Las cuotas live cambian minuto a minuto, por
    eso se usa un cache muy corto (45s) en lugar de los 600s del prematch.

    A diferencia de buscar_mejor_cuota (que usa /odds = prematch y devuelve
    cuotas estaticas de antes del partido), esta refleja el estado actual.

    Devuelve (cuota, casa) o (None, None) si no hay cuota live disponible.
    """
    odds = api_get(f"/odds/live?fixture={fixture_id}", use_cache=True, ttl=45)
    if not odds:
        return None, None

    PINNACLE_NAMES = {"Pinnacle", "Pinnacle Sports"}
    CASA_PRIORIDAD = {
        "Pinnacle": 1, "Pinnacle Sports": 1,
        "Bet365": 2, "bet365": 2,
        "William Hill": 3, "Betfair": 4,
        "888Sport": 5, "Dafabet": 6,
    }

    jugada_norm = _normalizar_jugada_para_matching(jugada)
    jugada_l = jugada_norm.lower()

    mejor = None
    mejor_book = None

    for casa in odds:
        # /odds/live tiene estructura: cada item con "odds" -> lista de mercados
        bookmakers = casa.get("bookmakers", [])
        if not bookmakers and casa.get("odds"):
            # Estructura alternativa de /odds/live
            bookmakers = [{"name": "Live", "bets": casa.get("odds", [])}]

        for book in bookmakers:
            book_name = book.get("name", "Live")
            for bet in book.get("bets", book.get("odds", [])):
                bet_name = bet.get("name", "") or bet.get("label", "")
                for value in bet.get("values", bet.get("odds", [])):
                    nombre = str(value.get("value", "") or value.get("name", ""))
                    odd_raw = value.get("odd", value.get("value"))
                    try:
                        odd = float(odd_raw)
                    except (ValueError, TypeError):
                        continue

                    match = False
                    # Goles over/under
                    if "over" in jugada_l and "gol" in jugada_l:
                        try:
                            linea = float(jugada_norm.split("Over")[-1].strip().split()[0])
                        except Exception:
                            linea = None
                        if linea is not None and "over" in nombre.lower():
                            import re as _re_l
                            mnum = _re_l.search(r"(\d+\.?\d*)", nombre)
                            if mnum and abs(float(mnum.group(1)) - linea) < 0.01:
                                match = True
                    elif "under" in jugada_l and "gol" in jugada_l:
                        try:
                            linea = float(jugada_norm.split("Under")[-1].strip().split()[0])
                        except Exception:
                            linea = None
                        if linea is not None and "under" in nombre.lower():
                            import re as _re_l2
                            mnum2 = _re_l2.search(r"(\d+\.?\d*)", nombre)
                            if mnum2 and abs(float(mnum2.group(1)) - linea) < 0.01:
                                match = True
                    # Corners / Tarjetas live
                    elif ("corner" in jugada_l or "tarjeta" in jugada_l) and ("over" in jugada_l or "under" in jugada_l):
                        tipo = "over" if "over" in jugada_l else "under"
                        try:
                            seg = jugada_norm.split("Over" if tipo == "over" else "Under")[-1]
                            linea = float(seg.strip().split()[0].replace(",", "."))
                        except Exception:
                            linea = None
                        es_mkt = (("corner" in bet_name.lower() and "corner" in jugada_l)
                                  or (("card" in bet_name.lower() or "booking" in bet_name.lower())
                                      and "tarjeta" in jugada_l))
                        if linea is not None and es_mkt and tipo in nombre.lower():
                            import re as _re_l3
                            mnum3 = _re_l3.search(r"(\d+\.?\d*)", nombre)
                            if mnum3 and abs(float(mnum3.group(1)) - linea) < 0.01:
                                match = True
                    # Resultado 1X2
                    elif jugada_l.strip() in ("1", "2", "x"):
                        mapa = {"1": ("home", "1"), "2": ("away", "2"), "x": ("draw", "x")}
                        claves = mapa[jugada_l.strip()]
                        if nombre.lower() in claves:
                            match = True

                    if match:
                        prio = CASA_PRIORIDAD.get(book_name, 50)
                        prio_mejor = CASA_PRIORIDAD.get(mejor_book, 99) if mejor_book else 99
                        if mejor is None or prio < prio_mejor:
                            mejor = odd
                            mejor_book = book_name

    if mejor:
        book_label = mejor_book if mejor_book in PINNACLE_NAMES else f"{mejor_book} (live)"
        return round(mejor, 3), book_label
    return None, None


def buscar_mejor_cuota(fixture_id, jugada):
    odds = api_get(f"/odds?fixture={fixture_id}", use_cache=True, ttl=600)

    # --- FIX 1: Doble Oportunidad calculada desde 1X2 de Pinnacle ---
    # Pinnacle no ofrece mercado DC directamente. Calculamos la cuota
    # equivalente matematicamente desde sus cuotas 1X2 (mas precisas).
    if jugada in ("1X", "X2", "12"):
        cuota_dc, book_dc = _cuota_doble_oportunidad_pinnacle(odds, jugada)
        if cuota_dc:
            return cuota_dc, book_dc
        # Si Pinnacle no tiene 1X2 tampoco, caer al fallback normal abajo

    mejor = None
    mejor_book = None

    # Orden de preferencia: Pinnacle primero, luego mejor disponible
    CASA_PRIORIDAD = {
        "Pinnacle": 1, "Pinnacle Sports": 1,
        "Bet365": 2, "bet365": 2,
        "William Hill": 3, "Betfair": 4,
        "888Sport": 5, "Dafabet": 6,
        "Bwin": 7, "Unibet": 8,
    }

    # --- FIX 2: Normalizar jugada antes del matching ---
    # Quita sufijos como " live", " restante", " HT" para que el matcher
    # encuentre la linea numerica correctamente en jugadas live.
    jugada_norm = _normalizar_jugada_para_matching(jugada)
    jugada_l = jugada_norm.lower()

    for casa in odds:
        for book in casa.get("bookmakers", []):
            book_name = book.get("name", "Book")

            for bet in book.get("bets", []):
                bet_name = bet.get("name", "")

                for value in bet.get("values", []):
                    nombre = str(value.get("value", ""))
                    odd_raw = value.get("odd")

                    try:
                        odd = float(odd_raw)
                    except Exception:
                        continue

                    match = False

                    # Goles Over/Under — verificar que el mercado sea de goles
                    GOALS_MARKETS = {"Goals Over/Under", "Total Goals", "Over/Under",
                                     "Goals", "Total", "Over Under"}
                    is_goals_market = any(gm.lower() in bet_name.lower()
                                         for gm in GOALS_MARKETS)

                    if "over" in jugada_l and "gol" in jugada_l:
                        try:
                            linea = float(jugada_norm.split("Over")[-1].strip().split()[0])
                        except Exception:
                            linea = None
                        if is_goals_market and linea is not None:
                            # Match exacto
                            if nombre.strip() in (f"Over {linea}", f"Over{linea}",
                                                   f"Over {linea:.1f}", f"Over {int(linea)}"):
                                match = True
                            # Pinnacle usa "Mas de X" en espanol a veces
                            elif nombre.strip() in (f"Mas de {linea}", f"Más de {linea}"):
                                match = True
                            # Match flexible: linea cercana ±0.5
                            else:
                                import re as _re_g
                                m_num = _re_g.search(r"(\d+\.?\d*)", nombre)
                                if m_num:
                                    val = float(m_num.group(1))
                                    if abs(val - linea) <= 0.5 and "over" in nombre.lower():
                                        match = True

                    elif "under" in jugada_l and "gol" in jugada_l:
                        try:
                            linea = float(jugada_norm.split("Under")[-1].strip().split()[0])
                        except Exception:
                            linea = None
                        if is_goals_market and linea is not None:
                            if nombre.strip() in (f"Under {linea}", f"Under{linea}",
                                                   f"Under {linea:.1f}", f"Under {int(linea)}"):
                                match = True
                            elif nombre.strip() in (f"Menos de {linea}", f"Menos de {int(linea)}"):
                                match = True
                            # Match flexible: linea cercana ±0.5
                            else:
                                import re as _re_g2
                                m_num2 = _re_g2.search(r"(\d+\.?\d*)", nombre)
                                if m_num2:
                                    val2 = float(m_num2.group(1))
                                    if abs(val2 - linea) <= 0.5 and "under" in nombre.lower():
                                        match = True

                    # Ambos marcan
                    elif "ambos marcan" in jugada_l or "btts" in jugada_l:
                        if ("Both Teams" in bet_name or "BTTS" in bet_name) and nombre.lower() in ["yes","si","sí"]:
                            match = True

                    # Doble oportunidad fallback (si Pinnacle no tenia 1X2)
                    # Otras casas usan "1X", "X2", "12"
                    elif jugada == "1X":
                        if "Double Chance" in bet_name and (
                            "1X" in nombre or "Home/Draw" in nombre or
                            "Home Draw" in nombre or "1 X" in nombre
                        ):
                            match = True
                    elif jugada == "X2":
                        if "Double Chance" in bet_name and (
                            "X2" in nombre or "Draw/Away" in nombre or
                            "Draw Away" in nombre or "X 2" in nombre
                        ):
                            match = True
                    elif jugada == "12":
                        if "Double Chance" in bet_name and (
                            "12" in nombre or "Home/Away" in nombre or
                            "Home Away" in nombre or "1 2" in nombre
                        ):
                            match = True

                    # --- FIX 3: Corners — matching mas flexible ---
                    elif "corner" in jugada_l and "over" in jugada_l:
                        try:
                            linea_c = float(jugada_norm.split("Over")[-1].strip().split()[0].replace(",", "."))
                        except Exception:
                            linea_c = None
                        CORNER_MARKETS = {"Corner", "Corners", "Asian Corners", "Total Corners"}
                        is_corner_market = any(cm.lower() in bet_name.lower() for cm in CORNER_MARKETS)
                        if is_corner_market and linea_c is not None:
                            import re as _re_c
                            m_c = _re_c.search(r"(\d+\.?\d*)", nombre)
                            if m_c and abs(float(m_c.group(1)) - linea_c) < 0.01 and "over" in nombre.lower():
                                match = True
                            elif nombre.strip() in (f"Over {linea_c}", f"Over{linea_c}",
                                                     f"Over {linea_c:.1f}", f"Over {int(linea_c)}"):
                                match = True

                    elif "corner" in jugada_l and "under" in jugada_l:
                        try:
                            linea_c = float(jugada_norm.split("Under")[-1].strip().split()[0].replace(",", "."))
                        except Exception:
                            linea_c = None
                        CORNER_MARKETS = {"Corner", "Corners", "Asian Corners", "Total Corners"}
                        is_corner_market = any(cm.lower() in bet_name.lower() for cm in CORNER_MARKETS)
                        if is_corner_market and linea_c is not None:
                            import re as _re_c2
                            m_c2 = _re_c2.search(r"(\d+\.?\d*)", nombre)
                            if m_c2 and abs(float(m_c2.group(1)) - linea_c) < 0.01 and "under" in nombre.lower():
                                match = True
                            elif nombre.strip() in (f"Under {linea_c}", f"Under{linea_c}",
                                                     f"Under {linea_c:.1f}", f"Under {int(linea_c)}"):
                                match = True

                    # --- FIX 3: Tarjetas — ampliar nombres de mercado aceptados ---
                    elif "tarjeta" in jugada_l and "over" in jugada_l:
                        try:
                            linea_t = float(jugada_norm.split("Over")[-1].strip().split()[0].replace(",", "."))
                        except Exception:
                            linea_t = None
                        CARD_MARKETS = {"Card", "Booking", "Yellow", "Total Cards",
                                        "Bookings", "Cards", "Total Bookings"}
                        is_card_market = any(cm.lower() in bet_name.lower() for cm in CARD_MARKETS)
                        if is_card_market and linea_t is not None:
                            import re as _re_t
                            m_t = _re_t.search(r"(\d+\.?\d*)", nombre)
                            if m_t and abs(float(m_t.group(1)) - linea_t) < 0.01 and "over" in nombre.lower():
                                match = True
                            elif nombre.strip() in (f"Over {linea_t}", f"Over{linea_t}",
                                                     f"Over {linea_t:.1f}", f"Over {int(linea_t)}"):
                                match = True

                    elif "tarjeta" in jugada_l and "under" in jugada_l:
                        try:
                            linea_t = float(jugada_norm.split("Under")[-1].strip().split()[0].replace(",", "."))
                        except Exception:
                            linea_t = None
                        CARD_MARKETS = {"Card", "Booking", "Yellow", "Total Cards",
                                        "Bookings", "Cards", "Total Bookings"}
                        is_card_market = any(cm.lower() in bet_name.lower() for cm in CARD_MARKETS)
                        if is_card_market and linea_t is not None:
                            import re as _re_t2
                            m_t2 = _re_t2.search(r"(\d+\.?\d*)", nombre)
                            if m_t2 and abs(float(m_t2.group(1)) - linea_t) < 0.01 and "under" in nombre.lower():
                                match = True
                            elif nombre.strip() in (f"Under {linea_t}", f"Under{linea_t}",
                                                     f"Under {linea_t:.1f}", f"Under {int(linea_t)}"):
                                match = True

                    # 1X2 - Pinnacle usa "Home", "Draw", "Away" o "1", "X", "2"
                    elif jugada_l.strip() in ("1", "local gana", "victoria local"):
                        if ("Match Winner" in bet_name or "1X2" in bet_name or
                            "Match Result" in bet_name or "Full Time Result" in bet_name) and (
                            nombre in ("Home", "1", "Home Team")
                        ):
                            match = True
                    elif jugada_l.strip() in ("2", "visitante gana", "victoria visitante"):
                        if ("Match Winner" in bet_name or "1X2" in bet_name or
                            "Match Result" in bet_name or "Full Time Result" in bet_name) and (
                            nombre in ("Away", "2", "Away Team")
                        ):
                            match = True
                    elif jugada_l.strip() in ("x", "empate"):
                        if ("Match Winner" in bet_name or "1X2" in bet_name or
                            "Match Result" in bet_name or "Full Time Result" in bet_name) and (
                            nombre in ("Draw", "X", "Tie")
                        ):
                            match = True

                    if match:
                        prioridad_actual = CASA_PRIORIDAD.get(book_name, 50)
                        prioridad_mejor = CASA_PRIORIDAD.get(mejor_book, 50) if mejor_book else 99
                        if mejor is None:
                            mejor = odd
                            mejor_book = book_name
                        elif prioridad_actual < prioridad_mejor:
                            mejor = odd
                            mejor_book = book_name

    return mejor, mejor_book


def calcular_stats_mercados(team_id, last=5):
    partidos = api_get(f"/fixtures?team={team_id}&last={last}")
    
    total_corners = 0
    total_cards = 0
    total_shots = 0
    total_sog = 0
    validos = 0

    for p in partidos:
        fixture_id = p["fixture"]["id"]
        stats = api_get(f"/fixtures/statistics?fixture={fixture_id}", use_cache=True, ttl=900)

        for team_data in stats:
            if team_data["team"]["id"] != team_id:
                continue

            corners = 0
            yellows = 0
            reds = 0
            shots = 0
            sog = 0

            for item in team_data.get("statistics", []):
                tipo = item.get("type")
                valor = item.get("value") or 0

                if tipo == "Corner Kicks":
                    corners = valor
                elif tipo == "Yellow Cards":
                    yellows = valor
                elif tipo == "Red Cards":
                    reds = valor
                elif tipo == "Total Shots":
                    shots = valor
                elif tipo == "Shots on Goal":
                    sog = valor

            total_corners += corners
            total_cards += yellows + (reds * 2)
            total_shots += shots
            total_sog += sog
            validos += 1

    if validos == 0:
        return None

    return {
        "corners_prom": total_corners / validos,
        "cards_prom": total_cards / validos,
        "shots_prom": total_shots / validos,
        "sog_prom": total_sog / validos,
    }



def analizar_estilo_corners(team_id, last=10):
    """
    Analiza el estilo de juego de un equipo para corners.
    Extrae: corners totales, tiros desde los costados (crosses),
    corners por minuto, y detecta si el equipo juega por los costados
    o por el centro. Usa los ultimos 10 partidos.
    Tambien analiza los ultimos 6 partidos como local/visitante.
    """
    partidos = api_get(f"/fixtures?team={team_id}&last={last}")
    if not partidos:
        return None

    total_corners = 0
    total_crosses = 0
    total_shots = 0
    total_sog = 0
    corners_por_partido = []
    validos = 0

    for p in partidos:
        fixture_id = p["fixture"]["id"]
        stats = api_get(
            f"/fixtures/statistics?fixture={fixture_id}",
            use_cache=True, ttl=900
        )
        if not stats:
            continue

        for team_data in stats:
            if team_data["team"]["id"] != team_id:
                continue
            corners_p = 0
            crosses_p = 0
            shots_p = 0
            sog_p = 0
            for item in team_data.get("statistics", []):
                tipo = item.get("type", "")
                try:
                    raw = item.get("value") or 0
                    val = float(str(raw).replace("%","").strip()) if raw else 0
                except Exception:
                    val = 0
                if tipo == "Corner Kicks":
                    corners_p = val
                elif tipo == "Total Shots":
                    shots_p = val
                elif tipo == "Shots on Goal":
                    sog_p = val
                # Buscar crosses si disponible
                elif tipo in ("Passes", "Crosses", "Total passes"):
                    if tipo == "Crosses":
                        crosses_p = val

            total_corners += corners_p
            total_crosses += crosses_p
            total_shots += shots_p
            total_sog += sog_p
            corners_por_partido.append(corners_p)
            validos += 1

    if validos == 0:
        return None

    corners_prom = round(total_corners / validos, 2)
    shots_prom = round(total_shots / validos, 2)

    # Detectar estilo: si crosses/shots ratio es alto = juega por costados
    estilo = "centro"
    if total_shots > 0 and (total_crosses / max(total_shots, 1)) > 0.3:
        estilo = "costados"

    # Varianza de corners (consistencia)
    if len(corners_por_partido) > 1:
        media = corners_prom
        varianza = sum((x - media)**2 for x in corners_por_partido) / len(corners_por_partido)
        desviacion = round(varianza**0.5, 2)
    else:
        desviacion = 0

    return {
        "corners_prom": corners_prom,
        "corners_max": max(corners_por_partido) if corners_por_partido else 0,
        "corners_min": min(corners_por_partido) if corners_por_partido else 0,
        "corners_desviacion": desviacion,
        "shots_prom": shots_prom,
        "estilo": estilo,  # "costados" o "centro"
        "partidos_analizados": validos,
    }


def calcular_corners_avanzado(home_id, away_id, home_name, away_name,
                               elapsed=0, home_ganando=None):
    """
    Analisis avanzado de corners considerando:
    - Estilo de juego de cada equipo (costados vs centro)
    - Media de corners de los ultimos 10 partidos
    - Presion adicional si el favorito va perdiendo
    - Minutos restantes y ritmo de corners esperado
    Retorna recomendaciones de corners con score y motivo detallado.
    """
    recomendaciones = []

    home_estilo = analizar_estilo_corners(home_id, last=10)
    away_estilo = analizar_estilo_corners(away_id, last=10)

    if not home_estilo or not away_estilo:
        return recomendaciones

    # Media total de corners del partido (ambos equipos)
    corners_prom_partido = home_estilo["corners_prom"] + away_estilo["corners_prom"]

    # Bonus por estilo de costados (generan mas corners)
    bonus_estilo = 0
    motivo_estilo = []
    if home_estilo["estilo"] == "costados":
        bonus_estilo += 1.2
        motivo_estilo.append(f"{home_name} juega por costados")
    if away_estilo["estilo"] == "costados":
        bonus_estilo += 1.0
        motivo_estilo.append(f"{away_name} juega por costados")

    corners_esperados = corners_prom_partido + bonus_estilo

    # Si hay partido en curso: proyectar corners restantes
    if elapsed and elapsed > 0:
        minutos_restantes = max(90 - elapsed, 0)
        ritmo_corner = corners_esperados / 90  # corners por minuto promedio

        # Bonus si favorito va perdiendo (presion = mas corners)
        if home_ganando is False:  # local va perdiendo
            ritmo_corner *= 1.4
            motivo_estilo.append(f"Local presiona por ir perdiendo (~1 corner c/10min)")
        elif home_ganando is True:  # visitante va perdiendo
            ritmo_corner *= 1.2
            motivo_estilo.append(f"Visitante presiona")

        corners_restantes = round(ritmo_corner * minutos_restantes, 1)
        motivo_estilo.append(
            f"Min {elapsed}' — proyeccion: {corners_restantes} corners restantes"
        )
    else:
        corners_restantes = corners_esperados
        motivo_estilo.append(
            f"Media: {round(corners_esperados,1)} corners por partido"
        )

    motivo = " | ".join(motivo_estilo)

    # Generar lineas de corners recomendadas
    lineas_posibles = [7.5, 8.5, 9.5, 10.5, 11.5]
    for linea in lineas_posibles:
        if corners_esperados >= linea + 1.5:
            prob = min(85, 55 + (corners_esperados - linea) * 5)
            score = round(min(9.5, 6.0 + (corners_esperados - linea) * 0.8), 1)
            riesgo = round(max(1, 4 - (corners_esperados - linea) * 0.5), 1)
            recomendaciones.append({
                "mercado": "Corners",
                "jugada": f"Corners Over {linea}",
                "prob": round(prob, 1),
                "score": score,
                "riesgo": riesgo,
                "confianza": etiqueta_confianza(score),
                "motivo": motivo,
                "cuota_minima": cuota_minima(prob/100, riesgo),
                "cuota": cuota_minima(prob/100, riesgo),
                "corners_esperados": corners_esperados,
                "home_estilo": home_estilo["estilo"],
                "away_estilo": away_estilo["estilo"],
            })

    # Ordenar por score descendente y retornar las 2 mejores
    recomendaciones.sort(key=lambda x: x["score"], reverse=True)
    return recomendaciones[:2]

def agregar_doble_oportunidad(recomendaciones, home, away, home_general, away_general, home_home, away_away):
    base_home = home_home or home_general
    base_away = away_away or away_general

    if not base_home or not base_away:
        return recomendaciones

    home_score = 0
    away_score = 0

    # Forma reciente
    home_score += base_home["gf_prom"] * 2
    away_score += base_away["gf_prom"] * 2

    # Solidez defensiva
    home_score += max(0, 2 - base_home["gc_prom"]) * 2
    away_score += max(0, 2 - base_away["gc_prom"]) * 2

    # Invicto reciente: W/D suma, L resta
    home_score += base_home["forma"].count("W") * 1.2
    home_score += base_home["forma"].count("D") * 0.7
    home_score -= base_home["forma"].count("L") * 1.1

    away_score += base_away["forma"].count("W") * 1.2
    away_score += base_away["forma"].count("D") * 0.7
    away_score -= base_away["forma"].count("L") * 1.1

    diferencia = home_score - away_score

    def add_dc(jugada, prob, score, riesgo, motivo):
        recomendaciones.append({
            "mercado": "Doble oportunidad",
            "jugada": jugada,
            "prob": prob,
            "score": score,
            "riesgo": riesgo,
            "confianza": etiqueta_confianza(score),
            "motivo": motivo,
            "cuota_justa": cuota_justa(prob),
            "cuota_minima": cuota_minima(prob, riesgo),
        })

    if diferencia >= 3:
        add_dc(
            f"1X ({home} o empate)",
            78,
            8.0,
            2.8,
            f"{home} muestra mejor forma reciente, mayor solidez y menor probabilidad de derrota."
        )

    elif diferencia <= -3:
        add_dc(
            f"X2 ({away} o empate)",
            78,
            8.0,
            2.8,
            f"{away} muestra mejor forma reciente, mayor solidez y menor probabilidad de derrota."
        )

    elif abs(diferencia) < 1.5:
        # Partido parejo: no forzamos doble oportunidad
        pass

    recomendaciones.sort(key=lambda x: (x["score"], x["prob"]), reverse=True)
    return recomendaciones


def agregar_mercados_extra_prematch(recomendaciones, home_id, away_id, home_general, away_general):
    # MERCADOS EXTRA PREMATCH DESACTIVADOS.
    # Esta funcion emitia corners, tarjetas y BTTS en prematch. Los tres
    # mercados fueron eliminados de la generacion:
    #   - BTTS: efectividad real 41.6%
    #   - Corners prematch: 33-40% (vs 79.5% en corners live)
    #   - Tarjetas: dependen del arbitro y del animo de los jugadores,
    #     factores que el modelo no mide; efectividad inestable.
    # La funcion se conserva (la llama preparar_analisis) pero ya no
    # agrega nada. Los picks prematch provienen solo de
    # obtener_recomendaciones (goles, doble oportunidad).
    return recomendaciones


def enriquecer_con_odds(fixture_id, recomendaciones):
    for r in recomendaciones:
        cuota, book = buscar_mejor_cuota(fixture_id, r["jugada"])

        r["cuota_api"] = cuota
        r["bookmaker"] = book

        if cuota:
            r["edge"] = edge_estimado(r["prob"], cuota)
            r["movimiento"] = guardar_snapshot_odds(
                fixture_id,
                r["jugada"],
                cuota
            )
        else:
            r["edge"] = None
            r["movimiento"] = None

    return recomendaciones

def preparar_analisis(fixture_id, incluir_odds=False, incluir_contexto=False):
    fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=False)

    if not fixture:
        return None

    fixture = fixture[0]

    league = fixture["league"]["name"]
    country = fixture["league"]["country"]

    home = fixture["teams"]["home"]["name"]
    away = fixture["teams"]["away"]["name"]

    home_id = fixture["teams"]["home"]["id"]
    away_id = fixture["teams"]["away"]["id"]

    fecha = fixture["fixture"]["date"]

    try:
        dt_partido = datetime.fromisoformat(fecha.replace("Z", "+00:00"))
        dt_peru = dt_partido - timedelta(hours=5)
        fecha_partido = dt_peru.strftime("%Y-%m-%d")
    except Exception:
        fecha_partido = fecha_hoy_peru()

    home_general = calcular_forma(home_id)
    away_general = calcular_forma(away_id)

    if incluir_contexto or incluir_odds:
        home_home = calcular_forma(home_id, "home")
        away_away = calcular_forma(away_id, "away")
    else:
        home_home = None
        away_away = None

    recomendaciones = obtener_recomendaciones(
        home_general,
        away_general,
        home_home,
        away_away
    )

    recomendaciones = agregar_doble_oportunidad(
    recomendaciones,
    home,
    away,
    home_general,
    away_general,
    home_home,
    away_away
    )

    recomendaciones = agregar_mercados_extra_prematch(
    recomendaciones,
    home_id,
    away_id,
    home_general,
    away_general
    )

    if incluir_odds:
        recomendaciones = enriquecer_con_odds(
            fixture_id,
            recomendaciones
        )

    # ── RECALIBRACION V14 ────────────────────────────────────────────
    # Se aplica DESPUES de enriquecer con odds para que el filtro de
    # cuota use la cuota real de mercado cuando exista.
    for r in recomendaciones:
        aplicar_recalibracion(r, liga=league)

    # Filtro de cuota minima: descarta picks que no pueden ser rentables.
    # Si no se consultaron odds, cuota_minima (teorica) sirve de proxy.
    recomendaciones = [
        r for r in recomendaciones if cuota_pick_suficiente(r)
    ]

    # Reordenar tras recalibrar. Ordenar solo por probabilidad recalibrada
    # es muy chato: la recalibracion colapsa los valores a pocas bandas
    # (62/78/88/94) y se generan grandes empates. Se ordena por VALOR
    # ESPERADO del pick = prob_recalibrada * cuota, un numero continuo que
    # ademas es la metrica que de verdad importa para el bank.
    def _clave_orden(x):
        prob = float(x.get("prob", 0) or 0) / 100.0
        cuota = (x.get("cuota_api") or x.get("cuota")
                 or x.get("cuota_minima") or 0)
        try:
            cuota = float(cuota)
        except (ValueError, TypeError):
            cuota = 0.0
        ve = prob * cuota          # valor esperado bruto
        return (ve, float(x.get("prob", 0) or 0))

    recomendaciones.sort(key=_clave_orden, reverse=True)

    return {
        "fixture_id": str(fixture_id),
        "home": home,
        "away": away,
        "league": league,
        "country": country,
        "hora": hora_peru(fecha),
        "fecha": fecha_partido,
        "home_general": home_general,
        "away_general": away_general,
        "home_home": home_home,
        "away_away": away_away,
        "recomendaciones": recomendaciones
    }


def guardar_pick_plano(pick):
    """
    Persiste un pick que ya viene en formato PLANO (claves jugada/score/etc
    en la raiz), como los que generan /analizar_all y /live_all.
    Centraliza la persistencia para que TODA jugada entre al mismo pipeline
    de resumen, aprendizaje, metricas y simulacion de bank.
    Evita duplicados por (fixture_id + jugada).
    """
    if not pick or not pick.get("fixture_id") or not pick.get("jugada"):
        return False

    picks = leer_json(PICKS_FILE)

    # Evitar duplicado: mismo fixture + misma jugada
    for p in picks:
        if (str(p.get("fixture_id")) == str(pick.get("fixture_id"))
                and p.get("jugada") == pick.get("jugada")):
            p["fecha_consulta"] = fecha_hora_peru()
            p["probabilidad"] = pick.get("prob", p.get("probabilidad"))
            p["score"] = pick.get("score", p.get("score"))
            p["riesgo"] = pick.get("riesgo", p.get("riesgo"))
            if pick.get("minuto") is not None:
                p["minuto_consulta"] = pick.get("minuto")
            guardar_json_lista(PICKS_FILE, picks)
            return True

    # Normalizar cuota
    _cuota = pick.get("cuota_api") or pick.get("cuota") or pick.get("cuota_minima") or 0
    try:
        _cuota = float(_cuota) if _cuota else 0.0
    except (ValueError, TypeError):
        _cuota = 0.0

    cuota_pinnacle = pick.get("cuota_api") or _cuota
    try:
        cuota_pinnacle = float(cuota_pinnacle) if cuota_pinnacle else 0
    except Exception:
        cuota_pinnacle = 0

    prob_val = float(pick.get("prob", 0) or pick.get("probabilidad", 0) or 0)
    edge_val = edge_estimado(prob_val, cuota_pinnacle) if cuota_pinnacle > 1.0 else None
    categoria_edge, _label = clasificar_edge(edge_val)
    ve_val = valor_esperado(prob_val, cuota_pinnacle) if cuota_pinnacle > 1.0 else None

    registro = {
        "fixture_id": str(pick.get("fixture_id")),
        "fecha": pick.get("fecha", pick.get("fecha_partido", fecha_hoy_peru())),
        "hora": pick.get("hora", ""),
        "fecha_partido": pick.get("fecha_partido", fecha_hoy_peru()),
        "country": pick.get("country", ""),
        "league": pick.get("league", ""),
        "partido": pick.get("partido", ""),
        "mercado": pick.get("mercado", ""),
        "jugada": pick.get("jugada", ""),
        "probabilidad": prob_val,
        "score": pick.get("score", 0),
        "riesgo": pick.get("riesgo", 0),
        "cuota_minima": _cuota,
        "cuota": cuota_pinnacle if cuota_pinnacle > 1.0 else _cuota,
        "cuota_pinnacle": cuota_pinnacle if cuota_pinnacle > 1.0 else None,
        "bookmaker": pick.get("bookmaker", ""),
        "edge": edge_val,
        "edge_categoria": categoria_edge,
        "valor_esperado": ve_val,
        "estado": "pendiente",
        "resultado_real": None,
        "tipo": pick.get("tipo", "prematch"),
        "minuto_consulta": pick.get("minuto"),
        "es_seleccion": pick.get("es_seleccion", False),
        "timestamp": fecha_hora_peru(),
    }
    picks.append(registro)
    guardar_json_lista(PICKS_FILE, picks)
    return True


def guardar_pick_automatico(data):
    """
    Guarda un pick prematch en picks_guardados.json.
    Acepta dos formatos y los unifica:
      A) Formato preparar_analisis: data tiene clave 'recomendaciones'.
      B) Formato plano (analizar_all): jugada/score/etc en la raiz.
    Delega la persistencia a guardar_pick_plano para que TODA jugada
    entre al mismo pipeline (resumen, aprendizaje, metricas, bank).
    """
    if not data:
        return False

    if data.get("recomendaciones"):
        top = data["recomendaciones"][0]
        pick = {
            "fixture_id": str(data.get("fixture_id", "")),
            "fecha": data.get("fecha", fecha_hoy_peru()),
            "hora": data.get("hora", ""),
            "fecha_partido": data.get("fecha_partido", data.get("fecha", fecha_hoy_peru())),
            "country": data.get("country", ""),
            "league": data.get("league", ""),
            "partido": f"{data.get('home','')} vs {data.get('away','')}",
            "mercado": top.get("mercado", ""),
            "jugada": top.get("jugada", ""),
            "prob": top.get("prob", 0),
            "score": top.get("score", 0),
            "riesgo": top.get("riesgo", 0),
            "cuota": top.get("cuota_minima", 0) or top.get("cuota", 0),
            "cuota_api": top.get("cuota_api"),
            "bookmaker": top.get("bookmaker", ""),
            "tipo": data.get("tipo", "prematch"),
        }
        return guardar_pick_plano(pick)
    elif data.get("jugada"):
        return guardar_pick_plano(data)
    return False


def guardar_pick_live_automatico(fixture_id, home, away, country, league, hora, sugerencia, minuto=None):
    picks = leer_json(PICKS_FILE)

    for p in picks:
        if (
            str(p.get("fixture_id")) == str(fixture_id)
            and p.get("jugada") == sugerencia["jugada"]
        ):
            p["fecha_consulta"] = fecha_hora_peru()
            p["minuto_consulta"] = minuto
            p["probabilidad"] = sugerencia["prob"]
            p["score"] = sugerencia["score"]
            p["riesgo"] = sugerencia["riesgo"]
            # PUNTO 5: refrescar la cuota live si llego una nueva
            _nueva_cuota = sugerencia.get("cuota_api") or sugerencia.get("cuota", 0)
            try:
                _nueva_cuota = float(_nueva_cuota)
            except (ValueError, TypeError):
                _nueva_cuota = 0.0
            if _nueva_cuota > 1.0:
                p["cuota"] = _nueva_cuota
                p["cuota_api"] = sugerencia.get("cuota_api")
                p["bookmaker"] = sugerencia.get("bookmaker", p.get("bookmaker", ""))
            guardar_json_lista(PICKS_FILE, picks)
            return

    _cuota_live = sugerencia.get("cuota", 0) or sugerencia.get("cuota_minima", 0) or 0
    try:
        _cuota_live = float(_cuota_live)
    except (ValueError, TypeError):
        _cuota_live = 0.0

    picks.append({
        "fixture_id": str(fixture_id),
        "fecha": fecha_hoy_peru(),
        "fecha_partido": fecha_hoy_peru(),
        "hora": hora,
        "country": country,
        "league": league,
        "partido": f"{home} vs {away}",
        "mercado": sugerencia["mercado"],
        "jugada": sugerencia["jugada"],
        "probabilidad": sugerencia["prob"],
        "score": sugerencia["score"],
        "riesgo": sugerencia["riesgo"],
        "cuota_minima": _cuota_live,
        "cuota": _cuota_live,
        "cuota_api": sugerencia.get("cuota_api"),
        "cuota_pinnacle": sugerencia.get("cuota_api") if sugerencia.get("bookmaker", "").startswith("Pinnacle") else None,
        "bookmaker": sugerencia.get("bookmaker", ""),
        "estado": "pendiente",
        "resultado_real": None,
        "tipo": "live",
        "minuto_consulta": minuto,
        "timestamp": fecha_hora_peru()
    })

    guardar_json_lista(PICKS_FILE, picks)


def evaluar_resultado_jugada(jugada, gh, ga):
    total = gh + ga

    if jugada == "Under 3.5 goles":
        return total <= 3

    if jugada == "Over 1.5 goles":
        return total >= 2

    if jugada == "Over 2.5 goles":
        return total >= 3

    if jugada == "Ambos marcan - Sí":
        return gh > 0 and ga > 0

    if jugada in ["Over 0.5 gol live", "Over 0.5 gol restante"]:
        return None

    if "Corners" in jugada:
        return None

    return None


def actualizar_resultados_automaticos():
    picks = leer_json(PICKS_FILE)
    cambios = 0

    for p in picks:
        estado_actual = p.get("estado", p.get("resultado", "pendiente"))

        if estado_actual not in ["pendiente", "pendiente_manual"]:
            continue

        fixture_id = p.get("fixture_id")
        fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=False)

        if not fixture:
            continue

        fixture = fixture[0]
        status = fixture["fixture"]["status"]["short"]

        # Corregir hora del pick si está mal (reconvertir de UTC a Peru)
        fecha_api = fixture["fixture"].get("date","")
        if fecha_api:
            hora_correcta = hora_peru(fecha_api)
            if p.get("hora","") != hora_correcta:
                p["hora"] = hora_correcta

        if status not in ["FT", "AET", "PEN"]:
            continue

        gh = fixture["goals"]["home"]
        ga = fixture["goals"]["away"]

        if gh is None or ga is None:
            continue

        jugada = p.get("jugada", "")
        total = gh + ga

        acierto = None

        corners_total = None
        tarjetas_total = None

        stats = api_get(f"/fixtures/statistics?fixture={fixture_id}", use_cache=False)

        if stats:
            total_corners = 0
            total_cards = 0

            for team_data in stats:
                for item in team_data.get("statistics", []):
                    tipo = item.get("type")
                    raw = item.get("value")

                    # La API puede devolver valores como string ("8"), porcentaje ("45%") o None
                    try:
                        if raw is None:
                            valor = 0
                        elif isinstance(raw, str):
                            valor = int(raw.replace("%", "").strip()) if raw.strip() not in ("", "-") else 0
                        else:
                            valor = int(raw)
                    except (ValueError, TypeError):
                        valor = 0

                    if tipo == "Corner Kicks":
                        total_corners += valor

                    elif tipo == "Yellow Cards":
                        total_cards += valor

                    elif tipo == "Red Cards":
                        total_cards += (valor * 2)

            corners_total = total_corners
            tarjetas_total = total_cards

        import re as _re_jug

        def _linea(txt):
            """Extrae el numero de linea de una jugada como 'Over 10.5'"""
            m = _re_jug.search(r"(\d+\.?\d*)", txt)
            return float(m.group(1)) if m else None

        jugada_lower = jugada.lower()

        # ── Goles ────────────────────────────────────────────────────────
        if "under" in jugada_lower and "gol" in jugada_lower:
            linea = _linea(jugada)
            acierto = total < linea if linea is not None else None

        elif "over" in jugada_lower and "gol" in jugada_lower:
            linea = _linea(jugada)
            acierto = total > linea if linea is not None else None

        elif "ambos marcan" in jugada_lower or "btts" in jugada_lower:
            if "no" in jugada_lower:
                acierto = not (gh > 0 and ga > 0)
            else:
                acierto = gh > 0 and ga > 0

        # ── Corners ──────────────────────────────────────────────────────
        elif "corner" in jugada_lower and "over" in jugada_lower:
            linea = _linea(jugada.split("Over")[-1])
            acierto = corners_total is not None and corners_total > linea if linea is not None else None

        elif "corner" in jugada_lower and "under" in jugada_lower:
            linea = _linea(jugada.split("Under")[-1])
            acierto = corners_total is not None and corners_total < linea if linea is not None else None

        # ── Tarjetas ─────────────────────────────────────────────────────
        elif "tarjeta" in jugada_lower and "over" in jugada_lower:
            linea = _linea(jugada.split("Over")[-1])
            acierto = tarjetas_total is not None and tarjetas_total > linea if linea is not None else None

        elif "tarjeta" in jugada_lower and "under" in jugada_lower:
            linea = _linea(jugada.split("Under")[-1])
            acierto = tarjetas_total is not None and tarjetas_total < linea if linea is not None else None

        # ── Resultado ────────────────────────────────────────────────────
        elif "1x" in jugada_lower:
            acierto = gh >= ga

        elif "x2" in jugada_lower:
            acierto = ga >= gh

        elif jugada_lower.strip() == "1" or "victoria local" in jugada_lower:
            acierto = gh > ga

        elif jugada_lower.strip() == "2" or "victoria visitante" in jugada_lower:
            acierto = ga > gh

        elif jugada_lower.strip() == "x" or "empate" in jugada_lower:
            acierto = gh == ga

        elif "12" in jugada_lower:
            acierto = gh != ga

        # ── HT (primer tiempo) ───────────────────────────────────────────
        elif "ht" in jugada_lower and "over" in jugada_lower:
            linea = _linea(jugada)
            acierto = total > linea if linea is not None else None

        if "Corners" in jugada:
            p["resultado_real"] = f"{corners_total} corners"

        elif "Tarjetas" in jugada:
            p["resultado_real"] = f"{tarjetas_total} tarjetas"

        else:
            p["resultado_real"] = f"{gh}-{ga}"

        if acierto is True:
            p["estado"] = "acierto"
            p["resultado"] = "acierto"
            cambios += 1

        elif acierto is False:
            p["estado"] = "fallo"
            p["resultado"] = "fallo"
            cambios += 1

        else:
            p["estado"] = "pendiente_manual"
            p["resultado"] = "pendiente_manual"

    guardar_json_lista(PICKS_FILE, picks)

    # Auto-actualizar combinadas si hubo cambios en picks
    if cambios > 0:
        try:
            _actualizar_resultado_combinada()
        except Exception:
            pass

    return picks, cambios


def resumen_historial():
    picks, cambios = actualizar_resultados_automaticos()

    def score_pick(p):
        try:
            return float(p.get("score", 0))
        except:
            return 0

    picks = sorted(
        picks,
        key=score_pick,
        reverse=True
    )

    if not picks:
        return "❌ No hay picks guardados."

    texto = "📋 HISTORIAL PICKS\n\n"

    hoy = fecha_hoy_peru()
    picks_hoy = [p for p in picks if p.get("fecha") == hoy]
    picks_manana = [p for p in picks if p.get("fecha") > hoy]
    picks = picks_hoy + picks_manana

    total = len(picks)
    ganados = len([p for p in picks if p.get("estado") == "acierto"])
    perdidos = len([p for p in picks if p.get("estado") == "fallo"])
    pendientes = len([p for p in picks if p.get("estado", "pendiente") in ["pendiente", "pendiente_manual"]])

    cerrados = ganados + perdidos
    efectividad = round((ganados / cerrados) * 100, 1) if cerrados > 0 else 0

    texto += (
        f"📊 RESUMEN DEL DÍA\n"
        f"📌 Jugadas analizadas: {total}\n"
        f"✅ Ganadas: {ganados}\n"
        f"❌ Perdidas: {perdidos}\n"
        f"⏳ Pendientes: {pendientes}\n"
        f"🎯 Efectividad: {efectividad}%\n\n"
    )

    if cambios > 0:
        texto += f"🔄 Resultados actualizados: {cambios}\n\n"

    for idx, p in enumerate(picks, 1):
        estado = p.get("estado", "pendiente")

        emoji = "🟡"
        if estado == "acierto":
            emoji = "🟢"
        elif estado == "fallo":
            emoji = "🔴"
        elif estado == "pendiente_manual":
            emoji = "🟠"

        texto += (
            f"{idx}. {emoji} {p.get('partido', 'Partido')}\n"
            f"📅 Fecha partido: {p.get('fecha', 'N/D')} | 🕒 Hora: {p.get('hora', 'N/D')}\n"
            f"🌍 País: {p.get('country', 'N/D')}\n"
            f"🏆 Liga: {p.get('league', 'N/D')}\n"
            f"📌 Tipo: {p.get('tipo', p.get('fuente', 'prematch')).upper()}\n"
            f"🎯 Mercado: {p.get('mercado', 'N/D')}\n"
            f"✅ Jugada: {p.get('jugada', 'N/D')}\n"
            f"📊 Prob: {p.get('probabilidad', 'N/D')}%\n"
            f"⭐ Score: {p.get('score', 'N/D')}/10 | "
            f"💰 Cuota: {p.get('cuota_minima', p.get('cuota', 'N/D'))}\n"
            f"⚠️ Riesgo: {p.get('riesgo', 'N/D')}/10\n"
            f"📌 Estado: {estado.upper()}\n"
        )

        if p.get("resultado_real"):
            texto += f"⚽ Resultado: {p['resultado_real']}\n"

        texto += "\n"

    return texto[:3900]


def texto_resumen(data):
    recs = data["recomendaciones"]

    texto = (
        f"⚽ {data['home']} vs {data['away']}\n"
        f"🏆 {data['country']} - {data['league']}\n"
        f"🕒 {data['hora']} Hora Perú\n\n"
    )

    if not recs:
        return texto + "⚠️ No hay jugada clara.\nRecomendación: NO apostar."

    top = recs[0]

    texto += (
        f"🎯 Mercado: {top['mercado']}\n"
        f"✅ Jugada: {top['jugada']}\n\n"
        f"⭐ Score: {top['score']}/10\n"
        f"⚠️ Riesgo: {top['riesgo']}/10\n"
        f"{top['confianza']}\n\n"
        f"💰 Entrar solo si cuota ≥ {top['cuota_minima']}\n\n"
        f"🧠 Resumen:\n{top['motivo']}\n\n"
        f"💾 Guardado automáticamente para seguimiento."
    )

    return texto[:3900]


def texto_detalle(data):
    texto = (
        f"⚽ {data['home']} vs {data['away']}\n"
        f"🏆 {data['country']} - {data['league']}\n"
        f"🕒 {data['hora']} Hora Perú\n\n"
        f"{bloque_stats(f'📊 General - {data['home']}', data['home_general'])}\n"
        f"{bloque_stats(f'📊 General - {data['away']}', data['away_general'])}\n"
        f"{bloque_stats(f'🏠 Casa - {data['home']}', data['home_home'])}\n"
        f"{bloque_stats(f'🛫 Fuera - {data['away']}', data['away_away'])}\n"
    )

    if not data["recomendaciones"]:
        texto += "\n⚠️ No hay jugada clara.\n"
    else:
        texto += "\n✅ Mercados detectados:\n"

        for r in data["recomendaciones"][:4]:
            texto += (
                f"\n🎯 Mercado: {r['mercado']}\n"
                f"✅ Jugada: {r['jugada']}\n"
                f"⭐ Score: {r['score']}/10\n"
                f"⚠️ Riesgo: {r['riesgo']}/10\n"
                f"💰 Cuota justa: {r['cuota_justa']}\n"
                f"💰 Cuota Pinnacle: {r.get('cuota_api') or r.get('cuota_minima','N/D')}\n"
                f"📈 Edge: {r.get('edge','N/D')}% ({r.get('edge_categoria','?')})\n"
            )

            if r.get("cuota_api"):
                texto += (
                    f"🏦 Cuota API: {r['cuota_api']} ({r['bookmaker']})\n"
                    f"📈 Edge: {r['edge']}%\n"
                )

                if r.get("movimiento"):
                    texto += f"📉 Movimiento cuota: {r['movimiento']}\n"

            texto += f"🧠 Motivo: {r['motivo']}\n"

    return texto[:3900]

def get_fixtures_by_leagues(leagues, title):
    today = fecha_hoy_peru()
    texto = f"{title} ({today}) 🌐\n"
    total = 0

    for league_name, data in leagues.items():
        fixtures = api_get(
            f"/fixtures?league={data['id']}&season={data['season']}&date={today}",
            use_cache=True,
            ttl=600
        )

        if fixtures:
            texto += f"\n🏆 {league_name}\n"

        for m in fixtures:
            texto += (
                f"⚽ {hora_peru(m['fixture']['date'])} | "
                f"{m['teams']['home']['name']} vs {m['teams']['away']['name']}\n"
                f"ID: {m['fixture']['id']}\n"
            )
            total += 1

    if total == 0:
        return "❌ No encontré partidos."

    return texto[:3900]


def obtener_partidos_configurados():
    today = fecha_hoy_peru()
    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)

    partidos = []

    for league_name, data in ligas.items():
        fixtures = api_get(
            f"/fixtures?league={data['id']}&season={data['season']}&date={today}",
            use_cache=True,
            ttl=600
        )

        for m in fixtures:
            status = m["fixture"]["status"]["short"]

            if status in ["CANC", "PST", "ABD"]:
                continue

            country = m["league"].get("country", "")
            league_name = f"{country} {m['league']['name']}"

            partidos.append({
                "id": m["fixture"]["id"],
                "home": m["teams"]["home"]["name"],
                "away": m["teams"]["away"]["name"],
                "league": league_name,
                "hour": hora_peru(m["fixture"]["date"]),
                "timestamp": m["fixture"]["timestamp"]
            })

            partidos.sort(
                key=lambda x: x.get("timestamp", 9999999999)
        )

    return partidos


def generar_top(score_minimo=7.5):
    oportunidades = []
    _umbral_prob_top = umbral_prob_desde_score_legado(score_minimo)

    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)

    today = fecha_hoy_peru()

    for _, data_liga in ligas.items():

        fixtures = api_get(
            f"/fixtures?league={data_liga['id']}&season={data_liga['season']}&date={today}",
            use_cache=True,
            ttl=600
        )

        for m in fixtures:

            status = m["fixture"]["status"]["short"]

            if status in ["FT", "AET", "PEN", "CANC", "ABD"]:
                continue

            fixture_id = str(m["fixture"]["id"])

            try:

                data = preparar_analisis(
                    fixture_id,
                    incluir_odds=True,
                    incluir_contexto=False
                )

                if not data or not data["recomendaciones"]:
                    continue

                top = data["recomendaciones"][0]

                # Criterio unico V14: filtrar por PROBABILIDAD recalibrada,
                # no por score crudo (tras recalibrar el score cambio de
                # rango). score_minimo se traduce a umbral de probabilidad.
                if float(top.get("prob", 0) or 0) < _umbral_prob_top:
                    continue

                oportunidades.append({
                    "id": fixture_id,
                    "home": data["home"],
                    "away": data["away"],
                    "league": data["league"],
                    "country": data.get("country", "N/D"),
                    "hour": data["hora"],
                    **top
                })

            except Exception as e:
                print("ERROR TOP:", e)

    # PUNTO 2: orden descendente (mejores primero). Antes faltaba reverse=True
    oportunidades.sort(
        key=lambda x: (float(x.get("score", 0) or 0),
                       -int(x.get("riesgo", 9) or 9),
                       float(x.get("prob", 0) or 0)),
        reverse=True,
    )

    return oportunidades[:10]

def _formatear_pick_mensaje(o, idx=None, mostrar_id=True):
    """
    Formatea un pick para mensaje Telegram con cuota Pinnacle y edge.
    Usado por /top, /elite, /top_manana, /elite_manana, /analizar, etc.
    """
    # Cuota: usar Pinnacle si existe, si no la calculada
    cuota_pin = o.get("cuota_api") or o.get("cuota_pinnacle") or 0
    try:
        cuota_pin = float(cuota_pin) if cuota_pin else 0
    except Exception:
        cuota_pin = 0
    cuota_calc = o.get("cuota_minima") or o.get("cuota") or 0
    try:
        cuota_calc = float(cuota_calc) if cuota_calc else 0
    except Exception:
        cuota_calc = 0

    cuota_mostrar = cuota_pin if cuota_pin > 1.0 else cuota_calc

    # --- FIX 4: Mostrar la casa real, no siempre "Pinnacle" ---
    bookmaker = o.get("bookmaker", "")
    PINNACLE_NAMES = {"Pinnacle", "Pinnacle Sports", "Pinnacle (DC calc)"}
    if cuota_pin > 1.0:
        if bookmaker in PINNACLE_NAMES or "Pinnacle" in str(bookmaker):
            book_str = " (Pinnacle)"
        elif bookmaker:
            book_str = f" ({bookmaker})"
        else:
            book_str = " (casas)"
    elif cuota_calc > 1.0:
        book_str = " (calc)"
    else:
        book_str = ""

    # Edge vs Pinnacle — solo calcular si la cuota es de Pinnacle
    prob = float(o.get("prob", 0) or 0)
    es_pinnacle = cuota_pin > 1.0 and (bookmaker in PINNACLE_NAMES or "Pinnacle" in str(bookmaker))
    edge_val = edge_estimado(prob, cuota_pin) if es_pinnacle else None
    cat_edge, label_edge = clasificar_edge(edge_val)

    # Emoji de edge
    if cat_edge == "EXCELENTE":
        edge_line = f"\U0001f4b9 *Edge Pinnacle: {label_edge}* [EXCELENTE]"
    elif cat_edge == "BUENO":
        edge_line = f"\U0001f4b9 Edge Pinnacle: {label_edge} [BUENO]"
    elif cat_edge == "LEVE":
        edge_line = f"\U0001f4b9 Edge Pinnacle: {label_edge}"
    elif cat_edge == "SIN VALOR":
        edge_line = f"\u26a0\ufe0f Sin valor vs Pinnacle ({label_edge})"
    else:
        edge_line = ""

    num_str = f"{idx}\u20e3 " if idx else ""
    partido = o.get("partido") or f"{o.get('home','')} vs {o.get('away','')}"
    league = o.get("league", o.get("liga",""))
    country = o.get("country","")
    hora = o.get("hora", o.get("hour",""))
    score = o.get("score","")
    riesgo = o.get("riesgo","")
    jugada = o.get("jugada","")
    mercado = o.get("mercado","")
    fixture_id = o.get("id", o.get("fixture_id",""))

    lineas = [
        f"{num_str}*{partido}*",
        f"\U0001f310 {country} | \U0001f3c6 {league} | \U0001f552 {hora}",
        f"\U0001f3af {jugada} ({mercado})",
        f"Score: {score}/10 | Riesgo: {riesgo} | Prob: {prob}%",
        f"\U0001f4b0 Cuota: {cuota_mostrar if cuota_mostrar else 'N/D'}{book_str}",
    ]
    if edge_line:
        lineas.append(edge_line)
    if mostrar_id and fixture_id:
        lineas.append(f"\U0001f4cc ID: {fixture_id}")

    return "\n".join(lineas)


def generar_top_fecha(fecha, score_minimo=7.5):
    oportunidades = []
    _umbral_prob_top = umbral_prob_desde_score_legado(score_minimo)

    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)

    partidos = obtener_fixtures_por_fecha(ligas, fecha)

    for p in partidos:
        try:
            data = preparar_analisis(
                str(p["id"]),
                incluir_odds=True,
                incluir_contexto=True
            )

            if not data or not data["recomendaciones"]:
                continue

            top = data["recomendaciones"][0]

            # Criterio unico V14: filtrar por probabilidad recalibrada.
            if float(top.get("prob", 0) or 0) < _umbral_prob_top:
                continue

            oportunidades.append({
                "id": p["id"],
                "home": p["home"],
                "away": p["away"],
                "league": p["league"],
                "country": p.get("country", "N/D"),
                "hour": p["hour"],
                **top
            })

        except Exception as e:
            print("ERROR TOP FECHA:", e)

    oportunidades.sort(
        key=lambda x: x["score"],
        reverse=True
    )

    return oportunidades

def extraer_stats_live(stats_response):
    stats = {}

    for team_data in stats_response:
        name = team_data["team"]["name"]

        stats[name] = {
            "shots_on_goal": 0,
            "shots_total": 0,
            "corners": 0,
            "dangerous_attacks": 0,
            "possession": 0,
            "yellow_cards": 0,
            "red_cards": 0,
        }

        for item in team_data.get("statistics", []):
            tipo = item.get("type")
            valor = item.get("value") or 0

            if isinstance(valor, str) and "%" in valor:
                try:
                    valor = int(valor.replace("%", ""))
                except Exception:
                    valor = 0

            if tipo == "Shots on Goal":
                stats[name]["shots_on_goal"] = valor
            elif tipo == "Total Shots":
                stats[name]["shots_total"] = valor
            elif tipo == "Corner Kicks":
                stats[name]["corners"] = valor
            elif tipo == "Dangerous Attacks":
                stats[name]["dangerous_attacks"] = valor
            elif tipo == "Ball Possession":
                stats[name]["possession"] = valor
            elif tipo == "Yellow Cards":
                stats[name]["yellow_cards"] = valor
            elif tipo == "Red Cards":
                stats[name]["red_cards"] = valor

    return stats


def calcular_xg_aproximado(shots, shots_on_goal):
    return round((shots * 0.04) + (shots_on_goal * 0.18), 2)


def detectar_favorito_por_stats(home, away, h_stats, a_stats, gh, ga):
    h_score = 0
    a_score = 0

    h_score += h_stats.get("shots_total", 0) * 0.4
    a_score += a_stats.get("shots_total", 0) * 0.4

    h_score += h_stats.get("shots_on_goal", 0) * 1.2
    a_score += a_stats.get("shots_on_goal", 0) * 1.2

    h_score += h_stats.get("dangerous_attacks", 0) * 0.08
    a_score += a_stats.get("dangerous_attacks", 0) * 0.08

    h_score += h_stats.get("corners", 0) * 0.8
    a_score += a_stats.get("corners", 0) * 0.8

    h_score += h_stats.get("possession", 0) * 0.03
    a_score += a_stats.get("possession", 0) * 0.03

    if gh > ga:
        h_score += 1
    elif ga > gh:
        a_score += 1

    if abs(h_score - a_score) < 2:
        return None, "parejo"

    if h_score > a_score:
        return "home", home

    return "away", away


def estado_favorito(fav_side, gh, ga):
    if fav_side is None:
        return "parejo"

    if fav_side == "home":
        diff = gh - ga
    else:
        diff = ga - gh

    if diff < 0:
        return "perdiendo"
    if diff == 0:
        return "empatando"
    if diff == 1:
        return "ganando_1"
    return "ganando_2_mas"


def presion_favorito_alta(fav_side, h_stats, a_stats):
    if fav_side == "home":
        fav = h_stats
    elif fav_side == "away":
        fav = a_stats
    else:
        return False

    return (
        fav.get("shots_total", 0) >= 6
        or fav.get("shots_on_goal", 0) >= 2
        or fav.get("corners", 0) >= 3
        or fav.get("dangerous_attacks", 0) >= 28
    )


def linea_corners_recomendada(total_corners, elapsed):
    if elapsed is None:
        return None

    if elapsed <= 30:
        if total_corners >= 3:
            return "Corners Over 8.5", 1.65

    if elapsed <= 55:
        if total_corners >= 7:
            return "Corners Over 10.5", 1.75
        if total_corners >= 6:
            return "Corners Over 9.5", 1.70
        if total_corners >= 5:
            return "Corners Over 8.5", 1.62

    if elapsed <= 75:
        if total_corners >= 9:
            return "Corners Over 11.5", 1.80
        if total_corners >= 8:
            return "Corners Over 10.5", 1.72
        if total_corners >= 7:
            return "Corners Over 9.5", 1.65

    if elapsed > 75:
        if total_corners >= 10:
            return "Corners Over 11.5", 1.70
        if total_corners >= 9:
            return "Corners Over 10.5", 1.60

    return None


def sugerir_live_goles(
    elapsed,
    gh,
    ga,
    total_shots,
    total_sog,
    total_corners,
    h_corners,
    a_corners,
    total_da,
    total_xg,
    fav_estado,
    fav_presion
):
    sugerencias = []

    if elapsed is None:
        return sugerencias

    goles_actuales = gh + ga
    corners_dominantes = max(h_corners, a_corners)

    intensidad_alta = (
        total_sog >= 3
        or total_shots >= 9
        or total_da >= 45
        or total_xg >= 1.2
        or total_corners >= 4
        or corners_dominantes >= 3
    )

    intensidad_muy_alta = (
        total_sog >= 5
        or total_shots >= 14
        or total_da >= 70
        or total_xg >= 1.8
        or total_corners >= 6
        or corners_dominantes >= 4
    )

    # 0-0 con intensidad: evaluar goles incluso antes del 60
    if goles_actuales == 0 and elapsed >= 25 and intensidad_alta:
        if elapsed >= 70:
            sugerencias.append({
                "mercado": "Goles restantes",
                "jugada": "Over 0.5 gol restante",
                "prob": 78,
                "score": 7.8,
                "riesgo": 4.0,
                "cuota": 1.65,
                "motivo": "0-0 avanzado, pero el partido mantiene intensidad ofensiva."
            })
        elif intensidad_muy_alta:
            sugerencias.append({
                "mercado": "Goles totales live",
                "jugada": "Over 1.5 goles live",
                "prob": 76,
                "score": 7.6,
                "riesgo": 4.2,
                "cuota": 1.70,
                "motivo": "0-0 con intensidad alta: tiros, presión, corners o xG aproximado favorable."
            })
        else:
            sugerencias.append({
                "mercado": "Goles restantes",
                "jugada": "Over 0.5 gol restante",
                "prob": 75,
                "score": 7.2,
                "riesgo": 4.5,
                "cuota": 1.60,
                "motivo": "0-0 con señales ofensivas suficientes para esperar al menos un gol."
            })

    # Si ya hubo gol y el favorito pierde o empata, buscar otro gol
    if goles_actuales >= 1 and elapsed >= 25:
        if fav_estado in ["perdiendo", "empatando"] and intensidad_alta:
            sugerencias.append({
                "mercado": "Goles restantes",
                "jugada": "Over 0.5 gol restante",
                "prob": 78,
                "score": 7.7,
                "riesgo": 4.1,
                "cuota": 1.65,
                "motivo": "El favorito no va ganando y mantiene necesidad ofensiva."
            })

        elif fav_estado == "ganando_1" and fav_presion and intensidad_muy_alta:
            sugerencias.append({
                "mercado": "Goles restantes",
                "jugada": "Over 0.5 gol restante",
                "prob": 74,
                "score": 7.1,
                "riesgo": 4.8,
                "cuota": 1.70,
                "motivo": "El favorito gana por uno, pero sigue atacando con presión clara."
            })

    return sugerencias

def sugerir_live_btts(
    elapsed,
    gh,
    ga,
    h_shots,
    a_shots,
    h_sog,
    a_sog,
    h_corners,
    a_corners,
    h_da,
    a_da
):
    sugerencias = []

    if elapsed is None:
        return sugerencias

    if gh > 0 and ga > 0:
        return sugerencias

    if gh == ga:
        return sugerencias

    if gh > ga:
        perdedor_shots = a_shots
        perdedor_sog = a_sog
        perdedor_corners = a_corners
        perdedor_da = a_da
    else:
        perdedor_shots = h_shots
        perdedor_sog = h_sog
        perdedor_corners = h_corners
        perdedor_da = h_da

    presion_perdedor = (
        perdedor_sog >= 2
        or perdedor_shots >= 6
        or perdedor_corners >= 3
        or perdedor_da >= 25
    )

    if elapsed >= 35 and presion_perdedor:
        sugerencias.append({
            "mercado": "Ambos marcan",
            "jugada": "Ambos marcan - Sí",
            "prob": 75,
            "score": 7.5,
            "riesgo": 4.0,
            "cuota": 1.70,
            "motivo": "El equipo que va perdiendo está generando presión suficiente para buscar el empate."
        })

    return sugerencias


def sugerir_live_tarjetas(elapsed, total_yellow, total_red, marcador_apretado):
    sugerencias = []

    if elapsed is None:
        return sugerencias

    total_cards = total_yellow + (total_red * 2)

    if elapsed <= 35 and total_cards >= 2 and marcador_apretado:
        sugerencias.append({
            "mercado": "Tarjetas",
            "jugada": "Tarjetas Over 3.5",
            "prob": 78,
            "score": 7.5,
            "riesgo": 3.5,
            "cuota": 1.55,
            "motivo": "Partido friccionado temprano y marcador competitivo (linea conservadora 3.5)."
        })

    elif elapsed <= 60 and total_cards >= 3:
        sugerencias.append({
            "mercado": "Tarjetas",
            "jugada": "Tarjetas Over 3.5",
            "prob": 80,
            "score": 7.7,
            "riesgo": 3.3,
            "cuota": 1.45,
            "motivo": "Alta frecuencia de tarjetas antes del tramo final (linea conservadora 3.5)."
        })

    return sugerencias

def sugerir_live_ht(
    elapsed,
    gh,
    ga,
    total_shots,
    total_sog,
    total_corners,
    h_corners,
    a_corners,
    total_da,
    total_xg,
    fav_estado,
    fav_presion
):
    sugerencias = []

    if elapsed is None:
        return sugerencias

    # Solo aplica para primer tiempo
    if elapsed > 44:
        return sugerencias

    goles_actuales = gh + ga
    corners_dominantes = max(h_corners, a_corners)

    intensidad_ht = (
        total_sog >= 2
        or total_shots >= 7
        or total_da >= 35
        or total_xg >= 0.9
        or total_corners >= 3
        or corners_dominantes >= 3
        or fav_presion
    )

    intensidad_ht_fuerte = (
        total_sog >= 3
        or total_shots >= 10
        or total_da >= 50
        or total_xg >= 1.2
        or total_corners >= 4
        or corners_dominantes >= 4
    )

    # Over 0.5 gol HT LIVE
    if (
        goles_actuales == 0
        and elapsed >= 25
        and intensidad_ht
    ):
        sugerencias.append({
            "mercado": "Goles HT Live",
            "jugada": "Over 0.5 gol HT Live",
            "prob": 74 if intensidad_ht_fuerte else 70,
            "score": 7.5 if intensidad_ht_fuerte else 7.0,
            "riesgo": 4.2 if intensidad_ht_fuerte else 4.8,
            "cuota": 1.65 if intensidad_ht_fuerte else 1.75,
            "motivo": (
                "Primer tiempo 0-0 con señales ofensivas activas: "
                "tiros, presión, corners o xG aproximado favorable."
            )
        })

    # Over corners HT
    if (
        elapsed <= 35
        and total_corners >= 3
        and (
            fav_estado in ["perdiendo", "empatando", "parejo"]
            or fav_presion
            or corners_dominantes >= 3
        )
    ):
        linea = "Corners HT Over 4.5"
        cuota = 1.65
        prob = 74
        score = 7.4
        riesgo = 4.2

        if total_corners >= 4 and elapsed <= 30:
            linea = "Corners HT Over 5.5"
            cuota = 1.75
            prob = 72
            score = 7.2
            riesgo = 4.8

        sugerencias.append({
            "mercado": "Corners HT",
            "jugada": linea,
            "prob": prob,
            "score": score,
            "riesgo": riesgo,
            "cuota": cuota,
            "motivo": (
                f"Hay {total_corners} corners al minuto {elapsed}. "
                "Ritmo temprano alto para corners en el primer tiempo."
            )
        })

    return sugerencias

def analizar_live_fixture(fixture_id, cache_ttl=0):
    """
    Analiza un partido en vivo.
    cache_ttl: si es > 0, las llamadas a la API usan cache con ese TTL
    (en segundos). El job de alertas lo usa para no repetir llamadas
    identicas en cada ciclo; los comandos bajo demanda usan 0 (sin cache)
    para tener siempre datos frescos.
    """
    _usar_cache = cache_ttl > 0
    fixture = api_get(f"/fixtures?id={fixture_id}",
                      use_cache=_usar_cache, ttl=cache_ttl or CACHE_TTL)

    if not fixture:
        return None

    m = fixture[0]

    home = m["teams"]["home"]["name"]
    away = m["teams"]["away"]["name"]

    country = m["league"]["country"]
    league = m["league"]["name"]
    hora = hora_peru(m["fixture"]["date"])

    gh = m["goals"]["home"] or 0
    ga = m["goals"]["away"] or 0

    elapsed = m["fixture"]["status"]["elapsed"]
    status = m["fixture"]["status"]["short"]

    if status not in ["1H", "2H", "HT", "ET", "LIVE"]:
        return {
            "texto": f"⚽ {home} vs {away}\n⚠️ No está en vivo.",
            "alerta": False,
            "score_live": 0,
            "sugerencias": []
        }

    stats = extraer_stats_live(
        api_get(f"/fixtures/statistics?fixture={fixture_id}",
                use_cache=_usar_cache, ttl=cache_ttl or CACHE_TTL)
    )

    hs = stats.get(home, {})
    aas = stats.get(away, {})

    h_shots = hs.get("shots_total", 0)
    a_shots = aas.get("shots_total", 0)
    h_sog = hs.get("shots_on_goal", 0)
    a_sog = aas.get("shots_on_goal", 0)
    h_corners = hs.get("corners", 0)
    a_corners = aas.get("corners", 0)
    h_da = hs.get("dangerous_attacks", 0)
    a_da = aas.get("dangerous_attacks", 0)
    h_poss = hs.get("possession", 0)
    a_poss = aas.get("possession", 0)
    h_yellow = hs.get("yellow_cards", 0)
    a_yellow = aas.get("yellow_cards", 0)
    h_red = hs.get("red_cards", 0)
    a_red = aas.get("red_cards", 0)

    total_shots = h_shots + a_shots
    total_sog = h_sog + a_sog
    total_corners = h_corners + a_corners
    total_da = h_da + a_da
    total_yellow = h_yellow + a_yellow
    total_red = h_red + a_red

    home_xg = calcular_xg_aproximado(h_shots, h_sog)
    away_xg = calcular_xg_aproximado(a_shots, a_sog)
    total_xg = round(home_xg + away_xg, 2)

    fav_side, fav_name = detectar_favorito_por_stats(home, away, hs, aas, gh, ga)
    fav_estado = estado_favorito(fav_side, gh, ga)
    fav_presion = presion_favorito_alta(fav_side, hs, aas)

    score_live = 0
    motivos = []

    if total_shots >= 14:
        score_live += 2
        motivos.append("volumen alto de tiros")
    elif total_shots >= 9:
        score_live += 1
        motivos.append("volumen medio de tiros")

    if total_sog >= 5:
        score_live += 2
        motivos.append("muchos tiros al arco")
    elif total_sog >= 3:
        score_live += 1
        motivos.append("algunos tiros al arco")

    if total_corners >= 7:
        score_live += 2
        motivos.append("ritmo alto de corners")
    elif total_corners >= 3:
        score_live += 1
        motivos.append("corners tempranos o activos")

    if total_da >= 70:
        score_live += 2
        motivos.append("ataques peligrosos altos")
    elif total_da >= 45:
        score_live += 1
        motivos.append("ataques peligrosos moderados")

    if total_xg >= 2.2:
        score_live += 2
        motivos.append("xG aproximado alto")
    elif total_xg >= 1.3:
        score_live += 1
        motivos.append("xG aproximado moderado")

    if total_yellow >= 5:
        score_live += 1
        motivos.append("partido friccionado")

    if total_red >= 1:
        score_live += 1
        motivos.append("roja puede abrir el partido")

    if max(h_poss, a_poss) >= 65:
        score_live += 1
        motivos.append("dominio fuerte de posesión")

    if elapsed and elapsed >= 60 and abs(gh - ga) <= 1:
        score_live += 1
        motivos.append("marcador apretado mantiene intensidad")

    if elapsed and elapsed <= 35 and abs(gh - ga) >= 2:
        score_live -= 2
        motivos.append("ventaja amplia puede bajar intensidad")

    score_live = round(clamp(score_live, 0, 10), 1)

    sugerencias = []

    # BTTS (Ambos marcan) ELIMINADO de live: efectividad real 38-41%.
    # TARJETAS ELIMINADO de live: dependen del arbitro y del animo de los
    # jugadores, factores que el modelo no mide.
    # Las funciones sugerir_live_btts y sugerir_live_tarjetas se conservan
    # definidas por compatibilidad, pero ya no se invocan.

    sugerencias.extend(
        sugerir_live_ht(
            elapsed,
            gh,
            ga,
            total_shots,
            total_sog,
            total_corners,
            h_corners,
            a_corners,
            total_da,
            total_xg,
            fav_estado,
            fav_presion
        )
    )

    corner_line = linea_corners_recomendada(total_corners, elapsed)

    if corner_line:
        jugada_corner, cuota_corner = corner_line

        favorito_no_relajado = (
            fav_estado in ["perdiendo", "empatando"]
            or (
                fav_estado == "ganando_1"
                and fav_presion
                and score_live >= 5
            )
            or fav_estado == "parejo"
        )

        if favorito_no_relajado and score_live >= 3:
            sugerencias.append({
                "mercado": "Corners",
                "jugada": jugada_corner,
                "prob": 76,
                "score": round(max(score_live, 7.0), 1),
                "riesgo": round(clamp(10 - max(score_live, 7.0), 2, 7), 1),
                "cuota": cuota_corner,
                "motivo": (
                    f"Hay {total_corners} corners al minuto {elapsed}. "
                    "El favorito no está relajado o aún mantiene presión suficiente."
                )
            })

    if sugerencias:
        sugerencias.sort(key=lambda x: (x["score"], x["prob"]), reverse=True)
        top_live = sugerencias[0]
        guardar_pick_live_automatico(
            fixture_id,
            home,
            away,
            country,
            league,
            hora,
            top_live,
            minuto=elapsed
        )

    texto = (
        f"⚡ LIVE: {home} vs {away}\n"
        f"🏆 {country} - {league}\n"
        f"⏱ Minuto: {elapsed}\n"
        f"⚽ Marcador: {gh}-{ga}\n\n"
        f"⭐ Score live: {score_live}/10\n"
        f"⚠️ Riesgo live: {round(clamp(10 - score_live, 1, 10), 1)}/10\n\n"
        f"📊 Datos clave:\n"
        f"🎯 Tiros al arco: {total_sog}\n"
        f"🚩 Corners: {total_corners}\n"
        f"🔥 Ataques peligrosos: {total_da}\n"
        f"📈 xG aprox: {total_xg}\n"
        f"📌 Posesión: {h_poss}% - {a_poss}%\n"
        f"🟨 Amarillas: {total_yellow} | 🟥 Rojas: {total_red}\n"
    )

    if fav_name:
        texto += f"⭐ Favorito/dominante detectado: {fav_name} ({fav_estado})\n"

    texto += "\n"

    if motivos:
        texto += "🧠 Lectura rápida:\n"
        for motivo in motivos[:4]:
            texto += f"• {motivo}\n"
        texto += "\n"

    if not sugerencias:
        texto += "⚠️ No hay oportunidad live clara."
    else:
        texto += "🚨 Oportunidades LIVE:\n"
        for s in sugerencias[:3]:
            texto += (
                f"\n🎯 Mercado: {s['mercado']}\n"
                f"✅ Jugada: {s['jugada']}\n"
                f"📊 Probabilidad: {s['prob']}%\n"
                f"⭐ Score: {s['score']}/10\n"
                f"⚠️ Riesgo: {s['riesgo']}/10\n"
                f"💰 Cuota Pinnacle: {s.get('cuota_api') or s.get('cuota','N/D')}\n"
                f"📈 Edge: {s.get('edge','N/D')}% ({s.get('edge_categoria','?')})\n"
                f"🧠 {s['motivo']}\n"
            )

        texto += "\n💾 Mejor jugada live guardada automáticamente."

    # =========================
    # GUARDAR PICKS LIVE
    # =========================

    if sugerencias:
        picks = leer_json(PICKS_FILE)

        for s in sugerencias[:1]:
            ya_existe = any(
                p.get("fixture_id") == fixture_id
                and p.get("jugada") == s["jugada"]
                and p.get("tipo") == "live"
                for p in picks
            )

            if ya_existe:
                continue

            picks.append({
                "tipo": "live",
                "fixture_id": fixture_id,
                "partido": f"{home} vs {away}",
                "mercado": s["mercado"],
                "jugada": s["jugada"],
                "probabilidad": s.get("prob"),
                "score": s.get("score"),
                "riesgo": s.get("riesgo"),
                "cuota": s.get("cuota"),
                "estado": "pendiente",
                "resultado": "pendiente",
                "minuto_detectado": elapsed,
                "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            })

        guardar_json_lista(PICKS_FILE, picks)

    return {
        "texto": texto[:3900],
        "score_live": score_live,
        "sugerencias": sugerencias,
        "alerta": score_live >= 7 and len(sugerencias) > 0
    }


def listar_live():
    fixtures = api_get("/fixtures?live=all", use_cache=False)

    if not fixtures:
        return "❌ No hay partidos live."

    texto = "🔴 PARTIDOS LIVE\n"

    for m in fixtures[:20]:
        texto += (
            f"\n⚽ {m['teams']['home']['name']} vs {m['teams']['away']['name']}\n"
            f"🏆 {m['league']['country']} - {m['league']['name']}\n"
            f"⏱ {m['fixture']['status']['elapsed']}' | {m['goals']['home']}-{m['goals']['away']}\n"
            f"📌 ID: {m['fixture']['id']}\n"
        )

    return texto[:3900]

def generar_pdf_resumen():
    picks, cambios = actualizar_resultados_automaticos()

    hoy = fecha_hoy_peru()
    picks = [p for p in picks if p.get("fecha") == hoy]

    def score_pick(p):
        try:
            return float(p.get("score", 0))
        except:
            return 0

    picks = sorted(picks, key=score_pick, reverse=True)

    total = len(picks)
    ganados = len([p for p in picks if p.get("estado") == "acierto"])
    perdidos = len([p for p in picks if p.get("estado") == "fallo"])
    pendientes = len([
        p for p in picks
        if p.get("estado", "pendiente") in ["pendiente", "pendiente_manual"]
    ])

    cerrados = ganados + perdidos
    efectividad = round((ganados / cerrados) * 100, 1) if cerrados > 0 else 0

    c = canvas.Canvas(_tmp_path("resumen_dia.pdf"), pagesize=A4)
    width, height = A4
    y = height - 50

    c.setFont("Helvetica-Bold", 16)
    c.drawString(40, y, "REPORTE DIARIO HARRYNINE")
    y -= 30

    c.setFont("Helvetica", 10)
    c.drawString(40, y, f"Fecha: {hoy}")
    y -= 18
    c.drawString(40, y, f"Jugadas analizadas: {total}")
    y -= 18
    c.drawString(40, y, f"Ganadas: {ganados}")
    y -= 18
    c.drawString(40, y, f"Perdidas: {perdidos}")
    y -= 18
    c.drawString(40, y, f"Pendientes: {pendientes}")
    y -= 18
    c.drawString(40, y, f"Efectividad: {efectividad}%")
    y -= 30
    
    for i, p in enumerate(picks, 1):
        lineas = [
            f"{i}. {p.get('partido', 'N/D')}",
            f"Fecha: {p.get('fecha', 'N/D')} | Hora: {p.get('hora', 'N/D')}{' | Min: ' + str(p.get('minuto_consulta', '')) + chr(39) if p.get('minuto_consulta') else ' Hora Peru'}",
            f"Pais: {p.get('country', 'N/D')} | Liga: {p.get('league', 'N/D')} | Tipo: {p.get('tipo', p.get('fuente', 'prematch')).upper()}",
            f"Mercado: {p.get('mercado', 'N/D')} | Jugada: {p.get('jugada', 'N/D')}",
            f"Prob: {p.get('probabilidad', 'N/D')}% | Score: {p.get('score', 'N/D')}/10 | Riesgo: {p.get('riesgo', 'N/D')}/10 | Cuota: {p.get('cuota_minima', p.get('cuota', 'N/D'))}",
            f"Estado: {p.get('estado', 'pendiente').upper()} | Resultado: {p.get('resultado_real', 'pendiente')}",
        ]

        for linea in lineas:
            if y < 120:
                c.showPage()
                y = height - 50
                c.setFont("Helvetica", 10)

            c.drawString(40, y, linea[:110])
            y -= 14

        y -= 10

    # ── Graficos matplotlib insertados via imagen ────────────────────
    # Generar graficos del dia como imagenes y dibujarlos en el canvas
    try:
        picks_graf = [p for p in picks if p.get("estado","").lower() in ("acierto","fallo","pendiente")]
        img_ef_dia = _grafico_efectividad_periodo(
            picks_graf, titulo=f"Efectividad del dia {hoy}",
            path_out=_tmp_path("tmp_resumen_ef.png")
        )
        if img_ef_dia and y > 200:
            from reportlab.lib.utils import ImageReader
            img_r = ImageReader(img_ef_dia)
            img_w, img_h = 480, 160
            if y - img_h < 60:
                c.showPage()
                y = height - 50
            c.drawImage(img_r, 40, y - img_h, width=img_w, height=img_h)
            y -= (img_h + 20)
            import os as _os
            if _os.path.exists(img_ef_dia):
                _os.remove(img_ef_dia)
    except Exception:
        pass

    img_pvl_dia = _grafico_prematch_vs_live(picks_graf, path_out=_tmp_path("tmp_resumen_pvl.png"))
    if img_pvl_dia:
        try:
            from reportlab.lib.utils import ImageReader
            img_r2 = ImageReader(img_pvl_dia)
            img_w2, img_h2 = 420, 160
            if y - img_h2 < 60:
                c.showPage()
                y = height - 50
            c.drawImage(img_r2, 40, y - img_h2, width=img_w2, height=img_h2)
            y -= (img_h2 + 20)
            import os as _os2
            if _os2.path.exists(img_pvl_dia):
                _os2.remove(img_pvl_dia)
        except Exception:
            pass

    # ── Seccion combinada del dia ────────────────────────────────────
    y -= 10
    c.setFont("Helvetica-Bold", 12)
    c.drawString(40, y, "COMBINADA DEL DIA")
    y -= 20
    c.setFont("Helvetica", 10)

    comb_hoy = None
    try:
        combinadas = leer_json(COMBINADAS_FILE)
        comb_hoy = next((c2 for c2 in combinadas if c2.get("fecha") == hoy), None)
    except Exception:
        pass

    if comb_hoy and not comb_hoy.get("sin_combinada") and comb_hoy.get("picks"):
        estado_comb = comb_hoy.get("estado", "pendiente").upper()
        c.drawString(40, y, f"Tipo: {'Triple' if comb_hoy.get('n_picks',0)==3 else 'Doble'} | Cuota: {comb_hoy.get('cuota_combinada','?')}x | Estado: {estado_comb}")
        y -= 14
        c.drawString(40, y, f"Score prom: {comb_hoy.get('score_promedio','?')} | Riesgo prom: {comb_hoy.get('riesgo_promedio','?')}")
        y -= 14
        for i, pk in enumerate(comb_hoy.get("picks", []), 1):
            cuota_p = pk.get("cuota") or pk.get("cuota_minima") or "?"
            linea = f"  {i}. {pk.get('partido','')} — {pk.get('jugada','')} | Score: {pk.get('score','')} | Cuota: {cuota_p}"
            c.drawString(40, y, linea[:110])
            y -= 14
        if comb_hoy.get("fallo_en"):
            c.drawString(40, y, f"  Fallo en: {comb_hoy.get('fallo_en','')}")
            y -= 14
    elif comb_hoy and comb_hoy.get("sin_combinada"):
        c.drawString(40, y, f"Sin combinada rentable: {comb_hoy.get('motivo','')}")
        y -= 14
    else:
        c.drawString(40, y, "No se genero combinada hoy (usa /combinada para generarla)")
        y -= 14

    c.save()

def _seccion_combinadas_historico(elements, fecha_inicio, fecha_fin, styles):
    """
    Agrega seccion de historial de combinadas al PDF semanal/mensual.
    Muestra: total, aciertos, fallos, cuota promedio, ganancia/perdida simulada.
    """
    from reportlab.lib.units import cm as _cm
    try:
        combinadas = leer_json(COMBINADAS_FILE)
    except Exception:
        return

    # Filtrar combinadas del periodo
    periodo = [
        c for c in combinadas
        if fecha_inicio <= (c.get("fecha") or "") <= fecha_fin
    ]

    if not periodo:
        return

    s_h2 = styles["Heading2"].clone("ch2")
    s_h2.fontSize = 11
    s_h2.textColor = colors.HexColor("#1A1A2E")
    s_h2.spaceBefore = 10
    s_h2.spaceAfter = 4
    elements.append(Paragraph("Historial de Combinadas del Periodo", s_h2))
    elements.append(Spacer(1, 4))

    total_c = len(periodo)
    aciertos_c = sum(1 for c in periodo if c.get("estado","").lower() == "acierto")
    fallos_c   = sum(1 for c in periodo if c.get("estado","").lower() == "fallo")
    pendientes_c = total_c - aciertos_c - fallos_c
    sin_comb_c = sum(1 for c in periodo if c.get("sin_combinada"))
    ef_c = round(aciertos_c / (aciertos_c+fallos_c) * 100, 1) if (aciertos_c+fallos_c) > 0 else None

    cuotas = [float(c.get("cuota_combinada",0) or 0) for c in periodo if not c.get("sin_combinada") and c.get("cuota_combinada")]
    cuota_prom = round(sum(cuotas)/len(cuotas), 2) if cuotas else None

    # Simulacion bank (stake 3% fijo de S/500)
    bank_sim = 500.0
    for c in sorted(periodo, key=lambda x: x.get("fecha","")):
        if c.get("sin_combinada") or c.get("estado","").lower() == "pendiente":
            continue
        cuota_c = float(c.get("cuota_combinada",1) or 1)
        stake_c = round(bank_sim * STAKE_COMBINADA, 2)
        if c.get("estado","").lower() == "acierto":
            bank_sim = round(bank_sim + stake_c*(cuota_c-1), 2)
        elif c.get("estado","").lower() == "fallo":
            bank_sim = round(bank_sim - stake_c, 2)
    resultado_sim = round(bank_sim - 500.0, 2)

    # Tabla resumen
    data_res = [
        ["Metrica", "Valor"],
        ["Total combinadas", str(total_c)],
        ["Sin combinada rentable", str(sin_comb_c)],
        ["Aciertos", str(aciertos_c)],
        ["Fallos", str(fallos_c)],
        ["Pendientes", str(pendientes_c)],
        ["Efectividad", f"{ef_c}%" if ef_c is not None else "Sin datos"],
        ["Cuota promedio", str(cuota_prom) if cuota_prom else "—"],
        ["Resultado simulado (bank S/500, stake 3%)", f"+S/ {resultado_sim}" if resultado_sim >= 0 else f"-S/ {abs(resultado_sim)}"],
    ]
    t_res = Table(data_res, colWidths=[9*_cm, 5*_cm], repeatRows=1)
    t_res.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0,0), (-1,0), colors.white),
        ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
        ("FONTSIZE", (0,0), (-1,-1), 9),
        ("ALIGN", (0,0), (-1,-1), "CENTER"),
        ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.HexColor("#F8F9FA"), colors.white]),
        ("GRID", (0,0), (-1,-1), 0.4, colors.HexColor("#DEE2E6")),
        ("TOPPADDING", (0,0), (-1,-1), 4),
        ("BOTTOMPADDING", (0,0), (-1,-1), 4),
        ("TEXTCOLOR", (1,-1), (1,-1),
         colors.HexColor("#27500A") if resultado_sim >= 0 else colors.HexColor("#A32D2D")),
        ("FONTNAME", (1,-1), (1,-1), "Helvetica-Bold"),
    ]))
    elements.append(t_res)
    elements.append(Spacer(1, 8))

    # Detalle de cada combinada
    data_det = [["Fecha", "Tipo", "Cuota", "Score prom", "Riesgo prom", "Estado", "Fallo en"]]
    for c in sorted(periodo, key=lambda x: x.get("fecha","")):
        if c.get("sin_combinada"):
            data_det.append([c.get("fecha",""), "Sin comb.", "—", "—", "—", "—", c.get("motivo","")[:30]])
            continue
        n = c.get("n_picks", len(c.get("picks",[])))
        data_det.append([
            c.get("fecha",""),
            "Triple" if n == 3 else "Doble",
            str(c.get("cuota_combinada","?")),
            str(c.get("score_promedio","?")),
            str(c.get("riesgo_promedio","?")),
            (c.get("estado","pendiente") or "pendiente").upper(),
            (c.get("fallo_en","") or "")[:25],
        ])

    t_det = Table(data_det, repeatRows=1,
                  colWidths=[2.5*_cm, 2*_cm, 2*_cm, 2.5*_cm, 2.5*_cm, 2.5*_cm, 4*_cm])
    t_det.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0,0), (-1,0), colors.white),
        ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
        ("FONTSIZE", (0,0), (-1,-1), 8),
        ("ALIGN", (0,0), (-1,-1), "CENTER"),
        ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.HexColor("#F8F9FA"), colors.white]),
        ("GRID", (0,0), (-1,-1), 0.3, colors.HexColor("#DEE2E6")),
        ("TOPPADDING", (0,0), (-1,-1), 3),
        ("BOTTOMPADDING", (0,0), (-1,-1), 3),
    ]))
    elements.append(t_det)
    elements.append(Spacer(1, 0.3*_cm))


def _anclas_efectividad(picks_todos):
    """
    Calcula efectividad real de picks score 9.0+ riesgo 1
    para medir si el bot es rentable para cobertura.
    """
    anclas = [p for p in picks_todos
              if float(p.get("score", 0) or 0) >= 9.0
              and float(p.get("riesgo", 10) or 10) <= 1
              and p.get("estado", "").lower() in ("acierto", "fallo")]
    if not anclas:
        return {"total": 0, "aciertos": 0, "fallos": 0, "efectividad": None}
    aciertos = sum(1 for p in anclas if p.get("estado", "").lower() == "acierto")
    ef = round(aciertos / len(anclas) * 100, 1)
    return {"total": len(anclas), "aciertos": aciertos,
            "fallos": len(anclas) - aciertos, "efectividad": ef}


def generar_pdf_reporte(picks, titulo, filename):
    from reportlab.lib.units import cm
    doc = SimpleDocTemplate(
        filename,
        pagesize=landscape(A4),
        rightMargin=1.5*cm,
        leftMargin=1.5*cm,
        topMargin=1.5*cm,
        bottomMargin=1.5*cm
    )

    styles = getSampleStyleSheet()
    elements = []

    # ── Cabecera ──────────────────────────────────────────────────────
    s_titulo = styles["Title"].clone("tt")
    s_titulo.fontSize = 15
    s_titulo.textColor = colors.HexColor("#1A1A2E")
    elements.append(Paragraph(f"<b>{titulo}</b>", s_titulo))
    elements.append(Paragraph(
        f"Generado: {fecha_hora_peru()} Hora Peru",
        styles["Normal"]
    ))
    elements.append(Spacer(1, 10))

    # ── Resumen general ───────────────────────────────────────────────
    total = len(picks)
    aciertos = len([p for p in picks if p.get("estado", "").lower() == "acierto"])
    fallos   = len([p for p in picks if p.get("estado", "").lower() == "fallo"])
    pendientes = total - aciertos - fallos
    efectividad = round(aciertos / (aciertos + fallos) * 100, 1) if (aciertos + fallos) > 0 else 0

    # Efectividad anclas (score 9.0+ riesgo 1)
    todos_picks = leer_json(PICKS_FILE)
    anc = _anclas_efectividad(todos_picks)
    UMBRAL = 87.0
    if anc["efectividad"] is not None:
        semaforo = "RENTABLE para cobertura" if anc["efectividad"] >= UMBRAL else "NECESITA AJUSTE — efectividad por debajo del umbral"
        anc_txt = (f"Picks ancla (9.0+ riesgo 1): {anc['total']} analizados | "
                   f"Aciertos: {anc['aciertos']} | Fallos: {anc['fallos']} | "
                   f"Efectividad: {anc['efectividad']}% | Umbral: {UMBRAL}% | {semaforo}")
    else:
        anc_txt = "Picks ancla (9.0+ riesgo 1): sin datos suficientes aun"

    data_resumen = [
        ["Metrica", "Valor"],
        ["Total picks", str(total)],
        ["Aciertos", str(aciertos)],
        ["Fallos", str(fallos)],
        ["Pendientes", str(pendientes)],
        ["Efectividad cerrada", f"{efectividad}%"],
        ["Efectividad anclas (9.0+ riesgo 1)", f"{anc['efectividad']}%" if anc["efectividad"] is not None else "Sin datos"],
        ["Umbral rentabilidad cobertura", f"{UMBRAL}%"],
        ["Estado sistema cobertura", semaforo if anc["efectividad"] is not None else "Sin datos suficientes"],
    ]
    t_res = Table(data_resumen, colWidths=[8*cm, 10*cm], repeatRows=1)
    t_res.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 8),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.HexColor("#F8F9FA"), colors.white]),
        ("GRID", (0, 0), (-1, -1), 0.3, colors.HexColor("#DEE2E6")),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        # Colorear fila de estado anclas
        ("TEXTCOLOR", (1, -1), (1, -1),
         colors.HexColor("#27500A") if anc.get("efectividad") and anc["efectividad"] >= UMBRAL
         else colors.HexColor("#A32D2D")),
        ("FONTNAME", (1, -1), (1, -1), "Helvetica-Bold"),
    ]))
    elements.append(t_res)
    elements.append(Spacer(1, 14))

    # ── Resumen por dia ───────────────────────────────────────────────
    s_h2 = styles["Heading2"].clone("h2")
    s_h2.fontSize = 10
    s_h2.textColor = colors.HexColor("#1A1A2E")
    elements.append(Paragraph("Resumen por Dia", s_h2))
    elements.append(Spacer(1, 4))

    dias = {}
    for p in picks:
        fecha = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if not fecha:
            continue
        if fecha not in dias:
            dias[fecha] = {"total": 0, "aciertos": 0, "fallos": 0, "pendientes": 0}
        estado = p.get("estado", "pendiente").lower()
        dias[fecha]["total"] += 1
        if estado == "acierto":
            dias[fecha]["aciertos"] += 1
        elif estado == "fallo":
            dias[fecha]["fallos"] += 1
        else:
            dias[fecha]["pendientes"] += 1

    data_dias = [["Fecha", "Total", "Aciertos", "Fallos", "Pendientes", "Efectividad"]]
    for fecha in sorted(dias.keys()):
        d = dias[fecha]
        cerr = d["aciertos"] + d["fallos"]
        ef = f"{round(d['aciertos']/cerr*100,1)}%" if cerr else "--"
        data_dias.append([
            fecha[5:] if len(fecha) == 10 else fecha,
            str(d["total"]), str(d["aciertos"]),
            str(d["fallos"]), str(d["pendientes"]), ef
        ])

    t_dias = Table(data_dias, repeatRows=1,
                   colWidths=[3*cm, 2*cm, 2.5*cm, 2*cm, 2.5*cm, 3*cm])
    t_dias.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 8),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.HexColor("#F8F9FA"), colors.white]),
        ("GRID", (0, 0), (-1, -1), 0.3, colors.HexColor("#DEE2E6")),
        ("TOPPADDING", (0, 0), (-1, -1), 3),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 3),
    ]))
    elements.append(t_dias)
    elements.append(Spacer(1, 14))

    # ── Listado completo de picks ─────────────────────────────────────
    elements.append(Paragraph("Historial Completo de Picks", s_h2))
    elements.append(Spacer(1, 4))

    picks_ord = sorted(picks, key=lambda p: (
        (p.get("fecha_partido") or p.get("fecha") or ""),
        p.get("hora", "")
    ))

    data = [[
        "Fecha", "Hora", "Pais", "Liga", "Partido",
        "Jugada", "Score", "Riesgo", "Resultado", "Estado"
    ]]

    ESTADO_COLORES = {
        "acierto": colors.HexColor("#D4EDDA"),
        "fallo":   colors.HexColor("#F8D7DA"),
    }
    row_colors = [colors.HexColor("#1A1A2E")]  # header

    for p in picks_ord:
        estado = p.get("estado", "pendiente").lower()
        fecha_raw = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        fecha_show = fecha_raw[5:] if len(fecha_raw) == 10 else fecha_raw
        data.append([
            fecha_show,
            p.get("hora", ""),
            p.get("country", "")[:10] if p.get("country") else "",
            (p.get("league") or p.get("liga") or "")[:15],
            (p.get("partido", ""))[:25],
            (p.get("jugada", ""))[:22],
            str(p.get("score", "")),
            str(p.get("riesgo", "")),
            str(p.get("resultado_real", ""))[:12],
            estado.upper()[:12],
        ])
        row_colors.append(ESTADO_COLORES.get(estado, colors.white))

    col_w = [2*cm, 1.8*cm, 2.2*cm, 3.5*cm, 5.5*cm, 5*cm, 1.5*cm, 1.8*cm, 2.5*cm, 2.5*cm]
    table = Table(data, repeatRows=1, colWidths=col_w)

    ts = [
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 7),
        ("TOPPADDING", (0, 0), (-1, -1), 3),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 3),
        ("GRID", (0, 0), (-1, -1), 0.25, colors.HexColor("#DEE2E6")),
    ]
    for i, col in enumerate(row_colors):
        if i == 0:
            continue
        ts.append(("BACKGROUND", (0, i), (-1, i), col))

    table.setStyle(TableStyle(ts))
    elements.append(table)

    # Graficos matplotlib
    elements.append(Spacer(1, 14))
    tmps_graf = _insertar_graficos_pdf(elements, picks_ord, prefijo="reporte", styles=styles)

    # Seccion combinadas historico
    elements.append(Spacer(1, 14))
    if picks_ord:
        fechas_ord = sorted([(p.get("fecha_partido") or p.get("fecha") or "")[:10] for p in picks_ord if (p.get("fecha_partido") or p.get("fecha"))])
        if fechas_ord:
            _seccion_combinadas_historico(elements, fechas_ord[0], fechas_ord[-1], styles)

    # Seccion prematch vs live
    elements.append(Spacer(1, 14))
    _seccion_prematch_live_pdf(elements, picks_ord, styles, None)

    doc.build(elements)

    # Limpiar temporales de graficos
    import os as _os
    for tmp in tmps_graf:
        try:
            if tmp and _os.path.exists(tmp):
                _os.remove(tmp)
        except Exception:
            pass

    return filename


def filtrar_picks_por_dias(dias):
    actualizar_resultados_automaticos()

    picks = leer_json(PICKS_FILE)
    hoy = fecha_peru_obj()
    limite = hoy - timedelta(days=dias)

    filtrados = []

    for p in picks:
        fecha_txt = p.get("fecha")

        try:
            fecha_p = datetime.strptime(fecha_txt, "%Y-%m-%d")
        except Exception:
            continue

        if fecha_p >= limite:
            filtrados.append(p)

    return filtrados


def filtrar_picks_mes_actual():
    actualizar_resultados_automaticos()

    picks = leer_json(PICKS_FILE)
    hoy = fecha_peru_obj()

    filtrados = []

    for p in picks:
        fecha_txt = p.get("fecha")

        try:
            fecha_p = datetime.strptime(fecha_txt, "%Y-%m-%d")
        except Exception:
            continue

        if fecha_p.year == hoy.year and fecha_p.month == hoy.month:
            filtrados.append(p)

    return filtrados

# ══════════════════════════════════════════════════════════════════════
# ALERTAS LIVE — sistema global de un solo job (ahorro de API)
# Antes: 1 job por usuario, cada 90s, sin cache -> 3 usuarios = 3x consumo.
# Ahora: 1 job global cada 150s, con cache; escanea UNA vez y notifica a
# todos los suscriptores. El consumo de API ya no escala con los usuarios.
# ══════════════════════════════════════════════════════════════════════

# Intervalo del escaneo live global (segundos). 150s es suficiente para
# alertas live y reduce el consumo frente a los 90s anteriores.
ALERTAS_INTERVALO = 150
# TTL de cache del escaneo live: algo menor que el intervalo para que
# cada ciclo traiga datos frescos pero cualquier otra llamada a
# /fixtures?live=all dentro de la ventana reuse el resultado.
ALERTAS_CACHE_TTL = 120


def cargar_suscriptores_alertas():
    """Lista de chat_ids suscritos a alertas live (persistida en disco)."""
    data = leer_json(ALERTAS_SUBS_FILE)
    if isinstance(data, list):
        return [c for c in data if c is not None]
    return []


def guardar_suscriptores_alertas(subs):
    """Persiste la lista de suscriptores (sin duplicados)."""
    unicos = sorted({c for c in subs if c is not None}, key=str)
    guardar_json_lista(ALERTAS_SUBS_FILE, unicos)
    return unicos


def suscribir_alerta(chat_id):
    """Anade un chat a la lista de alertas. True si quedo suscrito."""
    subs = cargar_suscriptores_alertas()
    if chat_id not in subs:
        subs.append(chat_id)
        guardar_suscriptores_alertas(subs)
    return True


def desuscribir_alerta(chat_id):
    """Quita un chat de la lista de alertas. True si estaba y se quito."""
    subs = cargar_suscriptores_alertas()
    if chat_id in subs:
        subs = [c for c in subs if c != chat_id]
        guardar_suscriptores_alertas(subs)
        return True
    return False


async def revisar_alertas_live(context: ContextTypes.DEFAULT_TYPE):
    """
    Job GLOBAL de alertas live. Escanea los partidos en vivo UNA sola vez
    y envia las alertas a todos los suscriptores. El escaneo usa cache, de
    modo que el consumo de API es el mismo con 1 o con N usuarios.
    """
    subs = cargar_suscriptores_alertas()
    if not subs:
        return  # nadie suscrito: no se gasta ni una llamada extra

    # Escaneo unico con cache (mejora de consumo de API).
    fixtures = api_get("/fixtures?live=all",
                        use_cache=True, ttl=ALERTAS_CACHE_TTL)
    if not fixtures:
        return

    # Detectar las alertas una sola vez (no por usuario).
    nuevas = []
    for m in fixtures:
        fixture_id = str(m["fixture"]["id"])
        if fixture_id in ALERTED_LIVE:
            continue
        analisis = analizar_live_fixture(fixture_id,
                                         cache_ttl=ALERTAS_CACHE_TTL)
        if analisis and analisis.get("alerta"):
            ALERTED_LIVE.add(fixture_id)
            nuevas.append(analisis["texto"])

    if not nuevas:
        return

    # Difundir a todos los suscriptores. Si un envio falla (chat borrado,
    # bot bloqueado), se quita ese suscriptor para no reintentar siempre.
    caidos = []
    for chat_id in subs:
        for texto in nuevas:
            try:
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=f"🚨 ALERTA AUTOMÁTICA LIVE\n\n{texto}"
                )
            except Exception:
                caidos.append(chat_id)
                break
    if caidos:
        restantes = [c for c in subs if c not in caidos]
        guardar_suscriptores_alertas(restantes)


async def enviar_reporte_semanal(context: ContextTypes.DEFAULT_TYPE):
    chat_id = context.job.chat_id
    picks = filtrar_picks_por_dias(7)

    if not picks:
        await context.bot.send_message(chat_id=chat_id, text="📄 No hay picks semanales para reportar.")
        return

    filename = _tmp_path("reporte_semanal_harrynine.pdf")
    generar_pdf_reporte(picks, "REPORTE SEMANAL HARRYNINE", filename)

    with open(filename, "rb") as f:
        await context.bot.send_document(
            chat_id=chat_id,
            document=f,
            caption="📄 Reporte semanal HarryNine"
        )


async def enviar_reporte_mensual(context: ContextTypes.DEFAULT_TYPE):
    chat_id = context.job.chat_id
    picks = filtrar_picks_mes_actual()

    if not picks:
        await context.bot.send_message(chat_id=chat_id, text="📄 No hay picks mensuales para reportar.")
        return

    filename = _tmp_path("reporte_mensual_harrynine.pdf")
    generar_pdf_reporte(picks, "REPORTE MENSUAL HARRYNINE", filename)

    with open(filename, "rb") as f:
        await context.bot.send_document(
            chat_id=chat_id,
            document=f,
            caption="📄 Reporte mensual HarryNine"
        )


async def enviar_rendimiento_nocturno(context: ContextTypes.DEFAULT_TYPE):
    """Job automático: genera PDF de rendimiento y lo envía cada noche a las 23:59 hora Perú."""
    chat_id = context.job.chat_id
    hoy = fecha_peru_obj()
    anio, mes = hoy.year, hoy.month

    try:
        datos = _calcular_rendimiento_mes(anio, mes)
        if not datos:
            await context.bot.send_message(
                chat_id=chat_id,
                text="Reporte nocturno: sin picks registrados este mes todavia."
            )
            return

        # Guardar snapshot para aprendizaje
        _guardar_snapshot_rendimiento(datos)
        _actualizar_resultado_combinada()
        _guardar_snapshot_aprendizaje()

        # Verificar si es ultimo dia del mes para resetear bank acumulado
        from datetime import datetime as _dt_mes, timedelta as _td_mes
        manana = (fecha_peru_obj() + _td_mes(days=1))
        if manana.month != fecha_peru_obj().month:
            # Hoy es el ultimo dia del mes
            _resetear_bank_acumulado_fin_mes()
            await context.bot.send_message(
                chat_id=chat_id,
                text=(
                    f"\U0001f4c5 *Cierre de mes — Bank reseteado*\n"
                    f"El bank acumulado se reinicia a S/ {BANK_INICIAL:.2f} para el nuevo mes.\n"
                    f"El resultado del mes queda guardado en el historial."
                ),
                parse_mode="Markdown"
            )

        # Alarma de resultados de ligas top del dia
        try:
            picks_alarm = leer_json(PICKS_FILE)
            hoy_alarm = fecha_hoy_peru()
            ligas_top = {
                "Premier League","La Liga","Bundesliga","Serie A","Ligue 1",
                "Champions League","UEFA Champions League","Copa Libertadores",
                "Copa Sudamericana","Liga 1","Bundesliga 2"
            }
            picks_top_hoy = [
                p for p in picks_alarm
                if (p.get("fecha_partido") or p.get("fecha",""))[:10] == hoy_alarm
                and p.get("estado","").lower() in ("acierto","fallo")
                and not p.get("alarma_liga_enviada")
                and (p.get("league","") or p.get("liga","")) in ligas_top
            ]
            if picks_top_hoy:
                aciertos_top = sum(1 for p in picks_top_hoy if p.get("estado","").lower()=="acierto")
                fallos_top = len(picks_top_hoy) - aciertos_top
                ef_top = round(aciertos_top/len(picks_top_hoy)*100,1)
                lineas_top = [
                    f"\U0001f3c6 *Resultados Ligas Top — {hoy_alarm}*",
                    f"\u2705 {aciertos_top} aciertos | \u274c {fallos_top} fallos | {ef_top}%",
                    "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
                ]
                for p in picks_top_hoy:
                    emoji_p = "\u2705" if p.get("estado","").lower()=="acierto" else "\u274c"
                    lineas_top.append(
                        f"{emoji_p} {p.get('partido','')} | {p.get('league',p.get('liga',''))}\n"
                        f"   {p.get('jugada','')} | Score: {p.get('score','')} | "
                        f"Resultado: {p.get('resultado_real','?')}"
                    )
                    p["alarma_liga_enviada"] = True
                msg_top = "\n".join(lineas_top)
                for cid in _CHAT_IDS_ALARMAS:
                    try:
                        await context.bot.send_message(
                            chat_id=cid, text=msg_top, parse_mode="Markdown"
                        )
                    except Exception:
                        pass
                guardar_json_lista(PICKS_FILE, picks_alarm)
        except Exception:
            pass

        # Enviar alarmas de combinadas cerradas
        combinadas_all = leer_json(COMBINADAS_FILE)
        for c in combinadas_all:
            if c.get("estado") in ("acierto", "fallo") and not c.get("alarma_enviada"):
                ticket = c.get("ticket_id", "")
                estado = c.get("estado","").upper()
                emoji_res = "\u2705" if estado == "ACIERTO" else "\u274c"
                cuota_c = c.get("cuota_combinada","?")
                picks_c = c.get("picks",[])
                lineas_alarm = [
                    f"{emoji_res} *RESULTADO COMBINADA*",
                    f"\U0001f39f Ticket: `{ticket}`",
                    f"Estado: *{estado}*",
                    f"Cuota: {cuota_c}x | Picks: {len(picks_c)}",
                ]
                if c.get("fallo_en"):
                    lineas_alarm.append(f"\u274c Fallo en: {c['fallo_en']}")
                for i, p in enumerate(picks_c, 1):
                    r = p.get("resultado_real") or p.get("estado","?")
                    lineas_alarm.append(f"  {i}. {p.get('partido','')} — {r}")
                msg_alarm = "\n".join(lineas_alarm)
                for cid in _CHAT_IDS_ALARMAS:
                    try:
                        await context.bot.send_message(
                            chat_id=cid,
                            text=msg_alarm,
                            parse_mode="Markdown"
                        )
                    except Exception:
                        pass
                c["alarma_enviada"] = True
        guardar_json_lista(COMBINADAS_FILE, combinadas_all)

        # Analisis de efectividad por minuto
        minuto_analisis = _analizar_efectividad_por_minuto()
        if minuto_analisis and minuto_analisis.get("mejor_rango"):
            agregar_json(APRENDIZAJE_FILE, {
                "tipo": "snapshot_minutos",
                "fecha": fecha_hora_peru(),
                "analisis": minuto_analisis,
            })

        # Generar y enviar PDF
        pdf_path = generar_pdf_rendimiento(datos)
        with open(pdf_path, "rb") as f:
            await context.bot.send_document(
                chat_id=chat_id,
                document=f,
                filename=f"Rendimiento_{anio}_{mes:02d}_dia{hoy.day:02d}.pdf",
                caption=f"Reporte automatico nocturno — {hoy.strftime('%d/%m/%Y')}"
            )

        # Resumen de texto
        roi_txt = f"+{datos['roi']}%" if datos["roi"] >= 0 else f"{datos['roi']}%"
        lucro = round(datos["bank_final"] - BANK_INICIAL, 2)
        lucro_txt = f"+S/ {lucro:.2f}" if lucro >= 0 else f"-S/ {abs(lucro):.2f}"
        mejor_m = max(datos["mercados"].items(),
                      key=lambda x: x[1]["efectividad"])[0] if datos["mercados"] else "--"
        h = datos["hoy"]
        ef_hoy = f"{h['efectividad']}%" if h["efectividad"] is not None else "Sin cerrados"

        # Calcular tendencia últimos 7 días
        ultimos_7 = [(f, d) for f, d in datos["dias"] if (d["aciertos"]+d["fallos"]) > 0][-7:]
        ef_serie = [d["aciertos"] / (d["aciertos"]+d["fallos"]) * 100
                    for _, d in ultimos_7 if (d["aciertos"]+d["fallos"]) > 0]
        if len(ef_serie) >= 2:
            tend = ef_serie[-1] - ef_serie[0]
            tend_txt = "Subiendo" if tend > 5 else "Bajando" if tend < -5 else "Estable"
        else:
            tend_txt = "Sin datos"

        msg = (
            f"\U0001f319 *Cierre del dia — {hoy.strftime('%d/%m/%Y')}*\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4c5 *Hoy:* \u2705 {h['aciertos']}  \u274c {h['fallos']}  \U0001f3af {ef_hoy}\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4ca *Mes acumulado:*\n"
            f"  Efectividad: *{datos['efectividad']}%*\n"
            f"  Tendencia 7d: {tend_txt}\n"
            f"  Mejor mercado: {mejor_m}\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4b0 Bank: S/ {datos['bank_final']:.2f} ({lucro_txt} | {roi_txt} ROI)\n"
            f"\U0001f9e0 Snapshot guardado para aprendizaje."
        )
        await context.bot.send_message(chat_id=chat_id, text=msg, parse_mode="Markdown")

        # Combinada del dia en el reporte nocturno
        comb_noc = _armar_combinada_del_dia()
        if comb_noc and not comb_noc.get("sin_combinada"):
            _guardar_combinada(comb_noc)
            msg_comb = _formato_combinada_telegram(comb_noc, bank_actual=datos["bank_final"])
            await context.bot.send_message(chat_id=chat_id, text=msg_comb, parse_mode="Markdown")

        try:
            os.remove(pdf_path)
        except Exception:
            pass

    except Exception as e:
        await context.bot.send_message(
            chat_id=chat_id,
            text=f"Error en reporte nocturno automatico: {e}"
        )


async def _check_combinadas_job(context: ContextTypes.DEFAULT_TYPE):
    """
    Job periodico cada 15 minutos.
    Actualiza resultados de picks y combinadas pendientes automaticamente.
    Si alguna combinada se cierra, notifica al chat.
    """
    try:
        # Verificar estado antes de actualizar
        combinadas_antes = leer_json(COMBINADAS_FILE)
        pendientes_antes = {
            c.get("ticket_id",""): c.get("estado","pendiente")
            for c in combinadas_antes
            if c.get("estado","pendiente") == "pendiente"
            and not c.get("sin_combinada")
        }

        if not pendientes_antes:
            return  # No hay pendientes, no hacer nada

        # Actualizar picks y combinadas
        actualizar_resultados_automaticos()
        _actualizar_resultado_combinada()

        # Verificar cuales cambiaron
        combinadas_despues = leer_json(COMBINADAS_FILE)
        chat_id = context.job.chat_id

        for c in combinadas_despues:
            ticket = c.get("ticket_id","")
            if ticket not in pendientes_antes:
                continue
            nuevo_estado = c.get("estado","pendiente")
            if nuevo_estado in ("acierto","fallo"):
                # Esta combinada acaba de cerrarse — notificar
                emoji = "\u2705" if nuevo_estado == "acierto" else "\u274c"
                cuota_c = c.get("cuota_combinada","?")
                subtipo = c.get("subtipo","pre").upper()
                n = c.get("n_picks", len(c.get("picks",[])))
                tipo_str = "TRIPLE" if n==3 else "DOBLE"

                lineas = [
                    f"{emoji} *RESULTADO COMBINADA — {nuevo_estado.upper()}*",
                    f"\U0001f39f Ticket: `{ticket}`",
                    f"[{subtipo}] {tipo_str} | Cuota: {cuota_c}x",
                ]
                if c.get("fallo_en"):
                    lineas.append(f"\u274c Fallo en: {c['fallo_en']}")

                for i, p in enumerate(c.get("picks",[]), 1):
                    estado_p = p.get("estado","?")
                    emoji_p = "\u2705" if estado_p=="acierto" else "\u274c" if estado_p=="fallo" else "\u23f3"
                    lineas.append(
                        f"  {i}. {emoji_p} {p.get('partido','')} | {p.get('jugada','')}"
                    )

                try:
                    await context.bot.send_message(
                        chat_id=chat_id,
                        text="\n".join(lineas),
                        parse_mode="Markdown"
                    )
                except Exception:
                    pass

    except Exception:
        pass


def programar_reportes(context: ContextTypes.DEFAULT_TYPE, chat_id):
    for job in context.job_queue.get_jobs_by_name(f"reporte_semanal_{chat_id}"):
        job.schedule_removal()

    for job in context.job_queue.get_jobs_by_name(f"reporte_mensual_{chat_id}"):
        job.schedule_removal()

    for job in context.job_queue.get_jobs_by_name(f"rendimiento_nocturno_{chat_id}"):
        job.schedule_removal()

    context.job_queue.run_daily(
        enviar_reporte_semanal,
        time=dtime(hour=21, minute=0),
        days=(6,),
        chat_id=chat_id,
        name=f"reporte_semanal_{chat_id}"
    )

    context.job_queue.run_daily(
        enviar_reporte_mensual,
        time=dtime(hour=21, minute=10),
        days=tuple(range(7)),
        chat_id=chat_id,
        name=f"reporte_mensual_{chat_id}"
    )

    # Reporte de rendimiento nocturno automático — 23:59 hora Perú (= 04:59 UTC)
    context.job_queue.run_daily(
        enviar_rendimiento_nocturno,
        time=dtime(hour=4, minute=59),
        days=tuple(range(7)),
        chat_id=chat_id,
        name=f"rendimiento_nocturno_{chat_id}"
    )

    # Job cada 15 minutos para actualizar combinadas pendientes
    for job in context.job_queue.get_jobs_by_name(f"check_combinadas_{chat_id}"):
        job.schedule_removal()

    context.job_queue.run_repeating(
        _check_combinadas_job,
        interval=900,  # cada 15 minutos
        first=60,
        chat_id=chat_id,
        name=f"check_combinadas_{chat_id}"
    )

    # Job cada 30 minutos para alertas de edge EXCELENTE
    for job in context.job_queue.get_jobs_by_name(f"alerta_edge_{chat_id}"):
        job.schedule_removal()

    context.job_queue.run_repeating(
        _alerta_edge_excelente_job,
        interval=1800,  # cada 30 minutos
        first=120,
        chat_id=chat_id,
        name=f"alerta_edge_{chat_id}"
    )

def obtener_fixtures_por_fecha(ligas, fecha):
    partidos = []

    for league_name, data_liga in ligas.items():
        fixtures = api_get(
            f"/fixtures?league={data_liga['id']}&season={data_liga['season']}&date={fecha}&timezone=America/Lima",
            use_cache=True,
            ttl=600
        )

        for m in fixtures:
            status = m["fixture"]["status"]["short"]

            if status in ["CANC", "PST", "ABD"]:
                continue

            country = data_liga.get("country", m["league"].get("country", ""))
            titulo_liga = f"{country} {league_name}".strip()

            partidos.append({
                "id": m["fixture"]["id"],
                "home": m["teams"]["home"]["name"],
                "away": m["teams"]["away"]["name"],
                "league": titulo_liga,
                "hour": hora_peru(m["fixture"]["date"]),
                "timestamp": m["fixture"]["timestamp"]
            })

    partidos.sort(key=lambda x: x.get("timestamp", 9999999999))
    return partidos

def texto_fixtures_fecha(titulo, ligas, fecha):
    partidos = obtener_fixtures_por_fecha(ligas, fecha)

    if not partidos:
        return f"❌ No encontré fixtures para {titulo}."

    texto = f"📅 {titulo} ({fecha})\n"

    liga_actual = ""

    for p in partidos:
        if p["league"] != liga_actual:
            liga_actual = p["league"]
            texto += f"\n🏆 {liga_actual}\n"

        texto += (
            f"⚽ {p['hour']} | {p['home']} vs {p['away']}\n"
            f"📌 ID: {p['id']}\n"
        )

    return texto[:3900]

async def fixtures_manana(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("📅 Buscando fixtures Europa + Sudamérica de mañana...")

    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)

    fecha = fecha_manana_peru()

    texto = texto_fixtures_fecha(
        "FIXTURES EUROPA + SUDAMÉRICA MAÑANA",
        ligas,
        fecha
    )

    await update.message.reply_text(texto[:3900])


async def top_manana(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("🏆 Buscando TOP prematch de mañana...")

    fecha = fecha_manana_peru()
    ops = generar_top_fecha(fecha, score_minimo=7.5)

    if not ops:
        await update.message.reply_text("❌ No encontré TOP prematch para mañana.")
        return

    lineas_t = ["\U0001f3c6 *TOP MA\u00d1ANA*"]
    for i, o in enumerate(ops[:10], 1):
        o["hora"] = o.get("hour","")
        o["partido"] = f"{o['home']} vs {o['away']}"
        o["fixture_id"] = o.get("id","")
        lineas_t.append("\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")
        lineas_t.append(_formatear_pick_mensaje(o, idx=i))

    await update.message.reply_text(
        "\n".join(lineas_t)[:4000], parse_mode="Markdown"
    )


async def elite_manana(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("🏆 Buscando ÉLITE prematch de mañana...")

    fecha = fecha_manana_peru()
    ops = generar_top_fecha(fecha, score_minimo=9)

    if not ops:
        await update.message.reply_text("❌ No encontré picks ÉLITE para mañana.")
        return

    lineas_e = ["\U0001f31f *\u00c9LITE MA\u00d1ANA*"]
    for i, o in enumerate(ops[:10], 1):
        o["hora"] = o.get("hour","")
        o["partido"] = f"{o['home']} vs {o['away']}"
        o["fixture_id"] = o.get("id","")
        lineas_e.append("\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")
        lineas_e.append(_formatear_pick_mensaje(o, idx=i))

    await update.message.reply_text(
        "\n".join(lineas_e)[:4000], parse_mode="Markdown"
    )

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    programar_reportes(context, chat_id)

    menu = (
        "🤖 *HarryNine V14* activo 😎🔥\n"
        "━━━━━━━━━━\n"
        "📋 *FIXTURES*\n"
        "/fixtures — Partidos de hoy (todas las ligas)\n"
        "/fixtures_manana — Manana todas\n"
        "━━━━━━━━━━\n"
        "🔍 *ANALISIS*\n"
        "/analizar_all — Analiza TODAS las ligas automaticamente\n"
        "/analizar ID — Analiza un partido especifico\n"
        "/detalle ID — Detalle completo de un partido\n"
        "/scanear — Escanea todas las ligas\n"
        "━━━━━━━━━━\n"
        "🎯 *PICKS PREMATCH*\n"
        "/top — Mejores picks de hoy (score 7.5+)\n"
        "/elite — Picks elite de hoy (score 9.0+)\n"
        "/top_manana — Mejores picks de manana\n"
        "/elite_manana — Picks elite de manana\n"
        "━━━━━━━━━━\n"
        "🔴 *PICKS LIVE*\n"
        "/live_all — Analiza TODOS los partidos live auto\n"
        "/live ID — Analisis de un partido live por ID\n"
        "/alertas_on — Activa alertas automaticas live\n"
        "/alertas_off — Desactiva alertas\n"
        "━━━━━━━━━━\n"
        "🎯 *COMBINADAS*\n"
        "/combinada — Combinada optima prematch del dia\n"
        "/combinada_live — Combinada optima picks live ahora\n"
        "/combinada_mixta — Combinada mixta prematch + live\n"
        "/comb3 — Combinada cuota 3x+ prematch\n"
        "/comb3_live — Combinada cuota 3x+ live\n"
        "/comb3_mixta — Combinada cuota 3x+ mixta\n"
        "/comb4 — Combinada 4x+ prematch (3-4 picks)\n"
        "/comb4_live — Combinada 4x+ live\n"
        "/comb4_mixta — Combinada 4x+ mixta\n"
        "/comb5 — Combinada 5x+ prematch (3-4 picks)\n"
        "/comb5_live — Combinada 5x+ live\n"
        "/comb5_mixta — Combinada 5x+ mixta\n"
        "━━━━━━━━━━\n"
        "📊 *REPORTES PDF*\n"
        "/resumen — Resumen del dia (todos los picks)\n"
        "/resumen_ayer — Resumen de ayer + combinadas\n"
        "/resumen_prematch — Solo picks prematch de hoy\n"
        "/resumen_live — Solo picks live de hoy\n"
        "/resumen_combinadas — Solo combinadas de hoy\n"
        "/estado — Dashboard rapido del dia\n"
        "/escalera — Escalera cronologica de picks\n"
        "/confirmar_escalera — Confirma la escalera\n"
        "/cancelar_escalera — Cancela la escalera activa\n"
        "/resumentop — Solo picks prematch\n"
        "/resumentoplive — Solo picks live\n"
        "/pdf_semana — Reporte semanal completo\n"
        "/pdf_mes — Reporte mensual completo\n"
        "/rendimiento — Reporte de rendimiento + bank\n"
        "━━━━━━━━━━\n"
        "🔧 *UTILIDADES*\n"
        "/feedback ID acierto — Marcar pick como acierto\n"
        "/feedback ID fallo — Marcar pick como fallo\n"
        "━━━━━━━━━━\n"
        "⏰ *REPORTES AUTOMATICOS*\n"
        "Semanal: domingos 9:00 PM hora Peru\n"
        "Mensual: diario 9:10 PM hora Peru\n"
        "Rendimiento nocturno: 11:59 PM hora Peru\n"
    )
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text(menu)


async def europa(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        get_fixtures_by_leagues(EUROPA_LEAGUES, "🇪🇺 Europa")
    )


async def sudamerica(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        get_fixtures_by_leagues(SUDAMERICA_LEAGUES, "🌎 Sudamérica")
    )


async def analizar(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.message.reply_text("Usa: /analizar ID")
        return

    fixture_id = context.args[0]

    fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=False)

    if not fixture:
        await update.message.reply_text("❌ No encontré el partido.")
        return

    status = fixture[0]["fixture"]["status"]["short"]

    if status in ["1H", "HT", "2H", "ET", "BT", "P", "LIVE"]:
        analisis_live = analizar_live_fixture(fixture_id)

        data_pre = preparar_analisis(
            fixture_id,
            incluir_odds=True,
            incluir_contexto=True
        )

        texto = "⚡ Detecté que el partido está EN VIVO.\n\n"

        if analisis_live:
            texto += analisis_live["texto"]

        if data_pre and data_pre.get("recomendaciones"):
            top_pre = data_pre["recomendaciones"][0]

            texto += (
                "\n\n📌 Soporte prematch:\n"
                    f"🎯 Mercado: {top_pre['mercado']}\n"
                    f"✅ Jugada: {top_pre['jugada']}\n"
                    f"⭐ Score prematch: {top_pre['score']}/10\n"
                    f"⚠️ Riesgo prematch: {top_pre['riesgo']}/10\n"
                    f"💰 Cuota justa: {top_pre.get('cuota_justa', 'N/D')}\n"
                    f"💰 Cuota Pinnacle: {top_pre.get('cuota_api') or top_pre.get('cuota_minima','N/D')}\n"
                    f"📈 Edge: {top_pre.get('edge','N/D')}% ({top_pre.get('edge_categoria','?')})\n"
                    f"🧠 {top_pre['motivo']}\n"
            )

            guardar_pick_automatico(data_pre)

            texto += "\n💾 Soporte prematch guardado automáticamente para seguimiento."

        await update.message.reply_text(texto[:3900])
        return

    if status in ["FT", "AET", "PEN"]:
        actualizar_resultados_automaticos()
        await update.message.reply_text(
            "⚠️ Este partido ya terminó. Actualicé resultados pendientes si correspondía. Usa /resumen."
        )
        return

    data = preparar_analisis(
        fixture_id,
        incluir_odds=True,
        incluir_contexto=True
    )

    if not data:
        await update.message.reply_text("❌ No encontré el partido.")
        return

    guardar_pick_automatico(data)
    await update.message.reply_text(texto_resumen(data))


async def detalle(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        await update.message.reply_text("Usa: /detalle ID")
        return

    fixture_id = context.args[0]

    await update.message.reply_text("⏳ Generando análisis profundo...")

    fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=False)

    if not fixture:
        await update.message.reply_text("❌ No encontré el partido.")
        return

    status = fixture[0]["fixture"]["status"]["short"]

    if status in ["1H", "HT", "2H", "ET", "BT", "P", "LIVE"]:
        analisis_live = analizar_live_fixture(fixture_id)

        data_pre = preparar_analisis(
            fixture_id,
            incluir_odds=True,
            incluir_contexto=True
        )

        texto = "⚡ DETALLE HÍBRIDO LIVE + PREMATCH\n\n"

        if analisis_live:
            texto += analisis_live["texto"]

        if data_pre:
            guardar_pick_automatico(data_pre)
            texto += "\n💾 Soporte prematch guardado automáticamente para seguimiento."

            texto += "\n\n📊 SOPORTE PREMATCH PROFUNDO\n\n"
            texto += texto_detalle(data_pre)

        await update.message.reply_text(texto[:3900])
        return

    data = preparar_analisis(
        fixture_id,
        incluir_odds=True,
        incluir_contexto=True
    )

    if not data:
        await update.message.reply_text("❌ No encontré el partido.")
        return

    guardar_pick_automatico(data)
    await update.message.reply_text(texto_detalle(data))


async def fixtures_ligas(update: Update, context: ContextTypes.DEFAULT_TYPE, leagues, titulo):
    await update.message.reply_text(f"📅 Buscando fixtures {titulo}...")

    today = fecha_hoy_peru()
    texto = f"📅 FIXTURES {titulo.upper()} ({today})\n"
    total = 0

    for league_name, data_liga in leagues.items():
        fixtures = api_get(
            f"/fixtures?league={data_liga['id']}&season={data_liga['season']}&date={today}&timezone=America/Lima",
            use_cache=True,
            ttl=600
        )

        partidos_liga = []

        for m in fixtures:
            status = m["fixture"]["status"]["short"]

            if status in ["CANC", "PST", "ABD"]:
                continue

            partidos_liga.append(
                f"⚽ {hora_peru(m['fixture']['date'])} | "
                f"{m['teams']['home']['name']} vs {m['teams']['away']['name']}\n"
                f"📌 ID: {m['fixture']['id']}"
            )
            total += 1

        if partidos_liga:
            country = data_liga.get("country", "")
            titulo_liga = f"{country} {league_name}".strip()
            
            texto += f"\n🏆 {data_liga.get('country', '')} {league_name}\n"
            texto += "\n".join(partidos_liga)
            texto += "\n"

    if total == 0:
        await update.message.reply_text(f"❌ No encontré fixtures en {titulo}.")
        return

    await update.message.reply_text(texto[:3900])


async def fixtures(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)
    await fixtures_ligas(update, context, ligas, "Europa + Sudamérica + Otras")


async def scanear_ligas(update: Update, context: ContextTypes.DEFAULT_TYPE, leagues, titulo):
    await update.message.reply_text(f"🔎 Escaneando {titulo}...")

    oportunidades = []

    today = fecha_hoy_peru()

    for league_name, data_liga in leagues.items():
        fixtures = api_get(
            f"/fixtures?league={data_liga['id']}&season={data_liga['season']}&date={today}",
            use_cache=True,
            ttl=600
        )

        for m in fixtures:
            status = m["fixture"]["status"]["short"]

            if status in ["FT", "AET", "PEN", "CANC", "ABD"]:
                continue

            fixture_id = str(m["fixture"]["id"])

            try:
                data = preparar_analisis(
                    fixture_id,
                    incluir_odds=False,
                    incluir_contexto=False
                )

                if not data or not data["recomendaciones"]:
                    continue

                mejor = data["recomendaciones"][0]

                if mejor["score"] < 7:
                    continue

                guardar_pick_automatico(data)

                oportunidades.append({
                    "fixture_id": fixture_id,
                    "partido": f"{data['home']} vs {data['away']}",
                    "league": data["league"],
                    "mercado": mejor["mercado"],
                    "jugada": mejor["jugada"],
                    "score": mejor["score"],
                    "riesgo": mejor["riesgo"],
                    "prob": mejor["prob"],
                    "cuota": mejor.get("cuota_minima", "N/D")
                })

            except Exception as e:
                print("ERROR SCAN:", e)

    oportunidades.sort(
        key=lambda x: (x["score"], -x["riesgo"], x["prob"]),
        reverse=True
    )

    if not oportunidades:
        await update.message.reply_text(f"❌ No encontré oportunidades fuertes en {titulo}.")
        return

    texto = f"🔎 ESCANEO {titulo.upper()}\n"

    for i, op in enumerate(oportunidades[:15], 1):
        texto += (
            f"\n{i}️⃣ {op['partido']}\n"
            f"🏆 {op['league']}\n"
            f"🎯 Mercado: {op['mercado']}\n"
            f"✅ Jugada: {op['jugada']}\n"
            f"📊 Prob: {op['prob']}%\n"
            f"⭐ Score: {op['score']}/10\n"
            f"⚠️ Riesgo: {op['riesgo']}/10\n"
            f"💰 Cuota Pinnacle: {op.get('cuota_api') or op.get('cuota','N/D')}\n"
            f"📈 Edge: {op.get('edge','N/D')}% ({op.get('edge_categoria','?')})\n"
            f"📌 ID: {op['fixture_id']}\n"
        )

    texto += "\n💾 Picks guardados automáticamente para tracking."

    await update.message.reply_text(texto[:3900])


async def scanear(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)

    await scanear_ligas(update, context, ligas, "Europa + Sudamérica + Otras")


async def elite(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("🏆 Buscando picks ÉLITE prematch...")

    ops = generar_top(score_minimo=9)

    if not ops:
        await update.message.reply_text("❌ No encontré picks ÉLITE prematch score 9+.")
        return

    texto = "🏆 PICKS ÉLITE PREMATCH\n"

    for i, o in enumerate(ops, 1):
        texto += (
            f"\n{i}️⃣ {o['home']} vs {o['away']}\n"
            f"🏆 {o['league']}\n"
            f"🎯 Mercado: {o['mercado']}\n"
            f"✅ Jugada: {o['jugada']}\n"
            f"📊 Prob: {o['prob']}%\n"
            f"⭐ Score: {o['score']}/10\n"
            f"⚠️ Riesgo: {o['riesgo']}/10\n"
            f"💰 Cuota Pinnacle: {o.get('cuota_api') or o.get('cuota_minima','N/D')}\n"
            f"📈 Edge: {o.get('edge','N/D')}% ({o.get('edge_categoria','?')})\n"
            f"📌 ID: {o['id']}\n"
        )

    await update.message.reply_text(texto[:3900])


async def top(update: Update, context: ContextTypes.DEFAULT_TYPE):
    ops = generar_top()

    ops = sorted(
    ops,
    key=lambda x: (
        -x["score"],
        x["riesgo"]
    )
)
    
    if not ops:
        await update.message.reply_text("❌ No encontré oportunidades fuertes.")
        return

    for o in ops:
        data_guardar = {
            "fixture_id": str(o["id"]),
            "fuente": "top",

            "fecha": fecha_hoy_peru(),
            "hora": o.get("hour", ""),
            "country": o.get("country", ""),
            "league": o.get("league", ""),
            "home": o["home"],
            "away": o["away"],
            "partido": f"{o['home']} vs {o['away']}",
            "recomendaciones": [{
                "mercado": o.get("mercado", ""),
                "jugada": o.get("jugada", ""),
                "prob": o.get("prob", "N/D"),
                "score": o.get("score", "N/D"),
                "riesgo": o.get("riesgo", "N/D"),
                "cuota_minima": o.get("cuota_minima", o.get("cuota", "N/D")),
                "cuota": o.get("cuota_minima", o.get("cuota", "N/D")),
                "cuota_justa": o.get("cuota_justa", "N/D"),
                "motivo": o.get("motivo", "")
            }]
        }

        guardar_pick_automatico(data_guardar)

    texto = "🏆 TOP OPORTUNIDADES\n"

    for i, o in enumerate(ops, 1):
        texto += (
            f"\n{i}️⃣ {o['home']} vs {o['away']}\n"
            f"🏆 {o['league']}\n"
            f"{obtener_bandera(o.get('country', ''))} País: {o.get('country', 'N/D')}\n"
            f"🕒 Hora: {o['hour']}\n"
            f"🎯 Mercado: {o['mercado']}\n"
            f"✅ Jugada: {o['jugada']}\n"
            f"⭐ Score: {o['score']}/10\n"
            f"⚠️ Riesgo: {o['riesgo']}/10\n"
            f"💰 Cuota Pinnacle: {o.get('cuota_api') or o.get('cuota_minima','N/D')}\n"
            f"📈 Edge: {o.get('edge','N/D')}% ({o.get('edge_categoria','?')})\n"
            f"📌 ID: {o['id']}\n"
        )

    texto += "\n💾 Picks TOP guardados automáticamente para tracking."

    await update.message.reply_text(texto[:3900])


async def alertas_on(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id

    # Limpiar cualquier job por-usuario heredado del esquema antiguo
    # (compatibilidad: instalaciones previas creaban un job con name=chat_id).
    for job in context.job_queue.get_jobs_by_name(str(chat_id)):
        job.schedule_removal()

    suscribir_alerta(chat_id)
    total = len(cargar_suscriptores_alertas())

    await update.message.reply_text(
        f"✅ Alertas LIVE activadas. El bot revisa cada "
        f"{ALERTAS_INTERVALO} segundos.\n"
        f"({total} usuario(s) suscrito(s) — el consumo de API es el mismo "
        f"para todos)."
    )


async def alertas_off(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id

    # Limpiar job heredado del esquema antiguo, si existiera.
    for job in context.job_queue.get_jobs_by_name(str(chat_id)):
        job.schedule_removal()

    estaba = desuscribir_alerta(chat_id)
    if estaba:
        await update.message.reply_text("🛑 Alertas LIVE desactivadas.")
    else:
        await update.message.reply_text(
            "ℹ️ No tenías alertas activas."
        )

def generar_pdf_resumentop():
    picks, cambios = actualizar_resultados_automaticos()

    hoy = fecha_hoy_peru()
    picks = [p for p in picks if p.get("fecha") == hoy and p.get("tipo", p.get("fuente", "")) in ["prematch", "top", "top_manana", "elite", "elite_manana"]]

    def score_pick(p):
        try:
            return float(p.get("score", 0))
        except:
            return 0

    picks = sorted(picks, key=score_pick, reverse=True)

    total = len(picks)
    ganados = len([p for p in picks if p.get("estado") == "acierto"])
    perdidos = len([p for p in picks if p.get("estado") == "fallo"])
    pendientes = len([p for p in picks if p.get("estado", "pendiente") in ["pendiente", "pendiente_manual"]])
    cerrados = ganados + perdidos
    efectividad = round((ganados / cerrados) * 100, 1) if cerrados > 0 else 0

    c = canvas.Canvas(_tmp_path("resumen_top.pdf"), pagesize=A4)
    width, height = A4
    y = height - 50

    c.setFont("Helvetica-Bold", 16)
    c.drawString(40, y, "REPORTE TOP PREMATCH HARRYNINE")
    y -= 30

    c.setFont("Helvetica", 10)
    c.drawString(40, y, f"Fecha: {hoy}")
    y -= 18
    c.drawString(40, y, f"Jugadas analizadas: {total}")
    y -= 18
    c.drawString(40, y, f"Ganadas: {ganados}")
    y -= 18
    c.drawString(40, y, f"Perdidas: {perdidos}")
    y -= 18
    c.drawString(40, y, f"Pendientes: {pendientes}")
    y -= 18
    c.drawString(40, y, f"Efectividad: {efectividad}%")
    y -= 30

    for i, p in enumerate(picks, 1):
        lineas = [
            f"{i}. {p.get('partido', 'N/D')}",
            f"Fecha: {p.get('fecha', 'N/D')} | Hora: {p.get('hora', 'N/D')}{' | Min: ' + str(p.get('minuto_consulta', '')) + chr(39) if p.get('minuto_consulta') else ' Hora Peru'}",
            f"Pais: {p.get('country', 'N/D')} | Liga: {p.get('league', 'N/D')} | Tipo: {p.get('tipo', p.get('fuente', 'prematch')).upper()}",
            f"Mercado: {p.get('mercado', 'N/D')} | Jugada: {p.get('jugada', 'N/D')}",
            f"Prob: {p.get('probabilidad', 'N/D')}% | Score: {p.get('score', 'N/D')}/10 | Riesgo: {p.get('riesgo', 'N/D')}/10 | Cuota: {p.get('cuota_minima', p.get('cuota', 'N/D'))}",
            f"Estado: {p.get('estado', 'pendiente').upper()} | Resultado: {p.get('resultado_real', 'pendiente')}",
        ]
        for linea in lineas:
            if y < 120:
                c.showPage()
                y = height - 50
                c.setFont("Helvetica", 10)
            c.drawString(40, y, linea[:110])
            y -= 14
        y -= 10

    c.save()


def generar_pdf_resumentoplive():
    picks, cambios = actualizar_resultados_automaticos()

    hoy = fecha_hoy_peru()
    picks = [p for p in picks if p.get("fecha") == hoy and p.get("tipo", p.get("fuente", "")) in ["live", "toplive", "elitelive"]]

    def score_pick(p):
        try:
            return float(p.get("score", 0))
        except:
            return 0

    picks = sorted(picks, key=score_pick, reverse=True)

    total = len(picks)
    ganados = len([p for p in picks if p.get("estado") == "acierto"])
    perdidos = len([p for p in picks if p.get("estado") == "fallo"])
    pendientes = len([p for p in picks if p.get("estado", "pendiente") in ["pendiente", "pendiente_manual"]])
    cerrados = ganados + perdidos
    efectividad = round((ganados / cerrados) * 100, 1) if cerrados > 0 else 0

    c = canvas.Canvas(_tmp_path("resumen_toplive.pdf"), pagesize=A4)
    width, height = A4
    y = height - 50

    c.setFont("Helvetica-Bold", 16)
    c.drawString(40, y, "REPORTE TOP LIVE HARRYNINE")
    y -= 30

    c.setFont("Helvetica", 10)
    c.drawString(40, y, f"Fecha: {hoy}")
    y -= 18
    c.drawString(40, y, f"Jugadas analizadas: {total}")
    y -= 18
    c.drawString(40, y, f"Ganadas: {ganados}")
    y -= 18
    c.drawString(40, y, f"Perdidas: {perdidos}")
    y -= 18
    c.drawString(40, y, f"Pendientes: {pendientes}")
    y -= 18
    c.drawString(40, y, f"Efectividad: {efectividad}%")
    y -= 30

    for i, p in enumerate(picks, 1):
        lineas = [
            f"{i}. {p.get('partido', 'N/D')}",
            f"Fecha: {p.get('fecha', 'N/D')} | Hora: {p.get('hora', 'N/D')}{' | Min: ' + str(p.get('minuto_consulta', '')) + chr(39) if p.get('minuto_consulta') else ' Hora Peru'}",
            f"Pais: {p.get('country', 'N/D')} | Liga: {p.get('league', 'N/D')} | Tipo: {p.get('tipo', p.get('fuente', 'live')).upper()}",
            f"Mercado: {p.get('mercado', 'N/D')} | Jugada: {p.get('jugada', 'N/D')}",
            f"Prob: {p.get('probabilidad', 'N/D')}% | Score: {p.get('score', 'N/D')}/10 | Riesgo: {p.get('riesgo', 'N/D')}/10 | Cuota: {p.get('cuota_minima', p.get('cuota', 'N/D'))}",
            f"Estado: {p.get('estado', 'pendiente').upper()} | Resultado: {p.get('resultado_real', 'pendiente')}",
        ]

        for linea in lineas:
            if y < 120:
                c.showPage()
                y = height - 50
                c.setFont("Helvetica", 10)
            c.drawString(40, y, linea[:110])
            y -= 14
        y -= 10

    c.save()

async def resumentop(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("📋 Generando reporte TOP prematch...")
    generar_pdf_resumentop()
    with open(_tmp_path("resumen_top.pdf"), "rb") as f:
        await update.message.reply_document(f)


async def resumentoplive(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("📋 Generando reporte TOP live...")
    generar_pdf_resumentoplive()
    with open(_tmp_path("resumen_toplive.pdf"), "rb") as f:
        await update.message.reply_document(f)

def construir_resumen_textual(picks, titulo="Resumen Diario"):
    """
    Construye un resumen textual compacto estilo Telegram a partir de una
    lista de picks. Calcula efectividad, profit/loss simulado, ROI, mejores
    y peores mercados, y agrega observaciones automaticas.
    """
    if not picks:
        return f"\U0001f4ca *{titulo}*\n\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\nSin picks registrados en el periodo."

    cerrados = [p for p in picks if p.get("estado") in ("acierto", "fallo")
                or p.get("resultado_real") in ("acierto", "fallo")]
    pendientes = [p for p in picks if p not in cerrados]

    def _es_acierto(p):
        return p.get("estado") == "acierto" or p.get("resultado_real") == "acierto"

    aciertos = [p for p in cerrados if _es_acierto(p)]
    fallos = [p for p in cerrados if not _es_acierto(p)]
    n_cerr = len(cerrados)
    efectividad = (len(aciertos) / n_cerr * 100) if n_cerr else 0.0

    # Simulacion profit/loss: stake fijo 1 unidad por pick cerrado
    profit = 0.0
    for p in cerrados:
        cuota = p.get("cuota") or p.get("cuota_pinnacle") or p.get("cuota_minima") or 0
        try:
            cuota = float(cuota)
        except Exception:
            cuota = 0
        if _es_acierto(p) and cuota > 1.0:
            profit += (cuota - 1)
        else:
            profit -= 1
    roi = (profit / n_cerr * 100) if n_cerr else 0.0

    # Mejor y peor mercado por efectividad
    por_mercado = {}
    for p in cerrados:
        mkt = p.get("mercado", "N/D") or "N/D"
        por_mercado.setdefault(mkt, {"ok": 0, "tot": 0})
        por_mercado[mkt]["tot"] += 1
        if _es_acierto(p):
            por_mercado[mkt]["ok"] += 1

    ranking = []
    for mkt, d in por_mercado.items():
        if d["tot"] >= 2:  # minimo 2 picks para ser representativo
            ranking.append((mkt, d["ok"] / d["tot"] * 100, d["tot"]))
    ranking.sort(key=lambda x: x[1], reverse=True)

    mejor_mkt = ranking[0] if ranking else None
    peor_mkt = ranking[-1] if len(ranking) > 1 else None

    # Bank simulado acumulado del mes
    try:
        bank_data = _leer_bank_acumulado()
        bank_actual = bank_data[-1].get("bank") if bank_data else BANK_INICIAL
    except Exception:
        bank_actual = BANK_INICIAL

    # Observaciones automaticas
    obs = []
    if efectividad >= 75:
        obs.append("Rendimiento solido, efectividad sobre objetivo.")
    elif efectividad >= 60:
        obs.append("Rendimiento aceptable, margen de mejora en seleccion.")
    elif n_cerr > 0:
        obs.append("Efectividad baja, revisar criterios de los picks.")
    if mejor_mkt:
        obs.append(f"El mercado {mejor_mkt[0]} fue el mas preciso ({mejor_mkt[1]:.0f}%).")
    if peor_mkt and peor_mkt[1] < 50:
        obs.append(f"El mercado {peor_mkt[0]} rindio por debajo del 50%, precaucion.")
    if roi > 0:
        obs.append(f"ROI positivo: cada unidad apostada genero retorno.")
    elif n_cerr > 0:
        obs.append("ROI negativo en el periodo.")
    if not obs:
        obs.append("Sin datos suficientes para un analisis detallado.")

    profit_emoji = "\U0001f7e2" if profit >= 0 else "\U0001f534"
    signo = "+" if profit >= 0 else ""

    lineas = [
        f"\U0001f4ca *{titulo}*",
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"\U0001f3b2 Total picks: {len(picks)}  (cerrados: {n_cerr} | pendientes: {len(pendientes)})",
        f"\u2705 Aciertos: {len(aciertos)}",
        f"\u274c Fallos: {len(fallos)}",
        f"\U0001f3af Efectividad: {efectividad:.1f}%",
        f"{profit_emoji} Profit: {signo}{profit:.2f} u",
        f"\U0001f4c8 ROI: {roi:+.1f}%",
        f"\U0001f3e6 Bank acumulado: S/ {bank_actual:.2f}",
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
    ]
    if mejor_mkt:
        lineas.append(f"\U0001f3c6 Mejor mercado: {mejor_mkt[0]} ({mejor_mkt[1]:.0f}%, {mejor_mkt[2]} picks)")
    if peor_mkt:
        lineas.append(f"\U0001f53b Peor mercado: {peor_mkt[0]} ({peor_mkt[1]:.0f}%, {peor_mkt[2]} picks)")
    lineas.append("")
    lineas.append("\U0001f9e0 *Analisis:*")
    for o in obs:
        lineas.append(f"\u2022 {o}")

    return "\n".join(lineas)


async def resumen(update: Update, context: ContextTypes.DEFAULT_TYPE):

    await update.message.reply_text("📄 Generando resumen del día...")

    # PUNTO 5: resumen textual estilo Telegram (sin abrir archivos)
    try:
        picks_hoy = [p for p in leer_json(PICKS_FILE)
                     if p.get("fecha") == fecha_hoy_peru()
                     or p.get("fecha_partido") == fecha_hoy_peru()]
        texto = construir_resumen_textual(picks_hoy, "Resumen Diario")
        await update.message.reply_text(texto, parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"⚠️ No se pudo generar el resumen textual: {e}")

    # PDF como complemento
    try:
        generar_pdf_resumen()
        with open(_tmp_path("resumen_dia.pdf"), "rb") as f:
            await update.message.reply_document(f)
    except Exception:
        pass


def _resumen_combinadas_texto(fecha):
    """
    Construye un bloque textual con el resumen de combinadas de una fecha.
    Devuelve string formateado para Telegram.
    """
    try:
        combinadas = leer_json(COMBINADAS_FILE)
    except Exception:
        return ""

    combs = [c for c in combinadas
             if (c.get("fecha", "") == fecha)
             and not c.get("sin_combinada")
             and c.get("picks")]

    if not combs:
        return "\U0001f3ab *Combinadas:* sin combinadas registradas ese dia."

    cerradas = [c for c in combs if c.get("estado", "").lower() in ("acierto", "fallo")]
    aciertos = [c for c in cerradas if c.get("estado", "").lower() == "acierto"]
    fallos = [c for c in cerradas if c.get("estado", "").lower() == "fallo"]
    pendientes = [c for c in combs if c not in cerradas]

    ef = (len(aciertos) / len(cerradas) * 100) if cerradas else 0.0

    # Simulacion de bank: stake 10% por combinada
    profit = 0.0
    for c in cerradas:
        cuota = float(c.get("cuota_combinada", 0) or 0)
        stake = 1.0  # 1 unidad por ticket
        if c.get("estado", "").lower() == "acierto" and cuota > 1.0:
            profit += stake * (cuota - 1)
        else:
            profit -= stake
    roi = (profit / len(cerradas) * 100) if cerradas else 0.0

    signo = "+" if profit >= 0 else ""
    emoji_p = "\U0001f7e2" if profit >= 0 else "\U0001f534"

    lineas = [
        "\U0001f3ab *Combinadas del dia:*",
        f"  Total: {len(combs)}  (cerradas: {len(cerradas)} | pendientes: {len(pendientes)})",
        f"  \u2705 Aciertos: {len(aciertos)}   \u274c Fallos: {len(fallos)}",
        f"  \U0001f3af Efectividad: {ef:.1f}%",
        f"  {emoji_p} Profit: {signo}{profit:.2f} u   \U0001f4c8 ROI: {roi:+.1f}%",
    ]
    return "\n".join(lineas)


async def resumen_ayer(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /resumen_ayer — resumen del dia anterior, incluye combinadas."""
    ayer = fecha_ayer_peru()
    await update.message.reply_text(f"\U0001f4c5 Generando resumen de ayer ({ayer})...")

    # Actualizar resultados antes de resumir
    try:
        actualizar_resultados_automaticos()
        _actualizar_resultado_combinada()
    except Exception:
        pass

    # Resumen de picks de ayer
    try:
        picks_ayer = [p for p in leer_json(PICKS_FILE)
                      if p.get("fecha") == ayer
                      or p.get("fecha_partido") == ayer]
        texto = construir_resumen_textual(picks_ayer, f"Resumen de Ayer — {ayer}")
    except Exception as e:
        texto = f"\u26a0\ufe0f No se pudo generar el resumen de picks: {e}"

    # Bloque de combinadas de ayer
    bloque_comb = _resumen_combinadas_texto(ayer)

    mensaje = texto + "\n\n" + bloque_comb
    await update.message.reply_text(mensaje, parse_mode="Markdown")


async def pdf_semana(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("⏳ Generando PDF semanal...")

    picks = filtrar_picks_por_dias(7)

    if not picks:
        await update.message.reply_text("❌ No hay picks semanales para generar PDF.")
        return

    filename = _tmp_path("reporte_semanal_harrynine.pdf")
    generar_pdf_reporte(picks, "REPORTE SEMANAL HARRYNINE", filename)

    with open(filename, "rb") as f:
        await update.message.reply_document(
            document=f,
            caption="📄 Reporte semanal HarryNine"
        )


async def pdf_mes(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("⏳ Generando PDF mensual...")

    picks = filtrar_picks_mes_actual()

    if not picks:
        await update.message.reply_text("❌ No hay picks mensuales para generar PDF.")
        return

    filename = _tmp_path("reporte_mensual_harrynine.pdf")
    generar_pdf_reporte(picks, "REPORTE MENSUAL HARRYNINE", filename)

    with open(filename, "rb") as f:
        await update.message.reply_document(
            document=f,
            caption="📄 Reporte mensual HarryNine"
        )


async def feedback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if len(context.args) < 2:
        await update.message.reply_text("Usa: /feedback ID acierto o /feedback ID fallo")
        return

    fixture_id = context.args[0]
    resultado = context.args[1].lower()

    if resultado not in ["acierto", "fallo"]:
        await update.message.reply_text("Resultado válido: acierto o fallo")
        return

    picks = leer_json(PICKS_FILE)
    actualizado = False

    for p in picks:
        if str(p.get("fixture_id")) == str(fixture_id):
            p["estado"] = resultado
            actualizado = True

    guardar_json_lista(PICKS_FILE, picks)

    agregar_json(FEEDBACK_FILE, {
        "fixture_id": fixture_id,
        "resultado": resultado,
        "fecha": fecha_hora_peru()
    })

    if actualizado:
        await update.message.reply_text(f"✅ Resultado actualizado: {resultado}")
    else:
        await update.message.reply_text("⚠️ Feedback guardado, pero no encontré ese pick en el historial.")


# ─────────────────────────────────────────────
#  /rendimiento — Reporte mensual de rendimiento
# ─────────────────────────────────────────────

REPORTE_FILE_TEMPLATE = _os_bot.path.join(BOT_DIR, "reporte_{year}_{month:02d}.json")
BANK_INICIAL = 500.0
STAKE_COMBINADA = 0.10  # 10% del bank para todas las combinadas


def _stake_pct(score, riesgo=None):
    """
    Devuelve el % del bank a apostar.
    Solo aplica para score >= 8.5 Y riesgo <= 2.
    Cualquier otro caso: no se simula apuesta (0.0).
    """
    if riesgo is not None and riesgo > 2:
        return 0.0
    if score >= 9.0:
        return 0.05
    elif score >= 8.5:
        return 0.03
    return 0.0


# ─────────────────────────────────────────────
#  SISTEMA DE APRENDIZAJE AUTOMATICO
# ─────────────────────────────────────────────

def _enriquecer_contexto_pick(fixture_id, league_id=None, season=None):
    """
    Extrae todas las variables contextuales disponibles via API-Football
    para enriquecer el pick antes de guardarlo en aprendizaje.json.
    Variables: arbitro, forma equipos, posicion tabla, lesionados,
    head2head, fatiga, prediccion API, odds movement.
    """
    ctx = {}
    try:
        # ── Fixture base ─────────────────────────────────────────────
        fixture_data = api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)
        if not fixture_data:
            return ctx
        fx = fixture_data[0]

        # Arbitro
        referee = fx.get("fixture", {}).get("referee", None)
        ctx["arbitro"] = referee.split(",")[0].strip() if referee else None

        # Venue / estadio
        venue = fx.get("fixture", {}).get("venue", {})
        ctx["estadio"] = venue.get("name", None)
        ctx["ciudad"] = venue.get("city", None)

        # Equipos IDs
        home_id = fx.get("teams", {}).get("home", {}).get("id")
        away_id = fx.get("teams", {}).get("away", {}).get("id")
        ctx["home_id"] = home_id
        ctx["away_id"] = away_id

        # Fecha y hora UTC
        fecha_utc = fx.get("fixture", {}).get("date", "")
        ctx["fecha_utc"] = fecha_utc

        # Dia de la semana (0=lunes, 6=domingo)
        if fecha_utc:
            try:
                from datetime import datetime as _dt
                dt = _dt.fromisoformat(fecha_utc.replace("Z", "+00:00"))
                ctx["dia_semana"] = dt.weekday()
                ctx["hora_utc"] = dt.hour
                ctx["es_finde"] = dt.weekday() >= 5
            except Exception:
                pass

        # ── Forma reciente de equipos (ultimos 5) ────────────────────
        for team_key, team_id in [("home", home_id), ("away", away_id)]:
            if not team_id:
                continue
            try:
                ultimos = api_get(
                    f"/fixtures?team={team_id}&last=5&status=FT",
                    use_cache=True, ttl=3600
                )
                if ultimos:
                    resultados = []
                    goles_favor = []
                    goles_contra = []
                    dias_descanso = []
                    for m in ultimos:
                        home_t = m["teams"]["home"]["id"] == team_id
                        gf = m["goals"]["home"] if home_t else m["goals"]["away"]
                        gc = m["goals"]["away"] if home_t else m["goals"]["home"]
                        winner = m["teams"]["home"]["winner"] if home_t else m["teams"]["away"]["winner"]
                        if winner is True: resultados.append("W")
                        elif winner is False: resultados.append("L")
                        else: resultados.append("D")
                        goles_favor.append(gf or 0)
                        goles_contra.append(gc or 0)
                        # Dias desde ese partido
                        try:
                            fecha_m = m["fixture"]["date"][:10]
                            from datetime import datetime as _dt2, date as _date
                            dias = (_date.today() - _dt2.strptime(fecha_m, "%Y-%m-%d").date()).days
                            dias_descanso.append(dias)
                        except Exception:
                            pass

                    ctx[f"{team_key}_forma"] = "".join(resultados)
                    ctx[f"{team_key}_goles_favor_prom"] = round(sum(goles_favor)/len(goles_favor), 2) if goles_favor else None
                    ctx[f"{team_key}_goles_contra_prom"] = round(sum(goles_contra)/len(goles_contra), 2) if goles_contra else None
                    ctx[f"{team_key}_dias_ultimo_partido"] = min(dias_descanso) if dias_descanso else None
                    ctx[f"{team_key}_racha_victorias"] = resultados.count("W")
            except Exception:
                pass

        # ── Posicion en tabla ────────────────────────────────────────
        if league_id and season:
            try:
                standings = api_get(
                    f"/standings?league={league_id}&season={season}",
                    use_cache=True, ttl=7200
                )
                if standings:
                    for group in standings:
                        for team_st in group:
                            tid = team_st.get("team", {}).get("id")
                            if tid == home_id:
                                ctx["home_posicion"] = team_st.get("rank")
                                ctx["home_puntos"] = team_st.get("points")
                                ctx["home_partidos_jugados"] = team_st.get("all", {}).get("played")
                            elif tid == away_id:
                                ctx["away_posicion"] = team_st.get("rank")
                                ctx["away_puntos"] = team_st.get("points")
                                ctx["away_partidos_jugados"] = team_st.get("all", {}).get("played")
            except Exception:
                pass

        # ── Lesionados y suspendidos ─────────────────────────────────
        try:
            injuries = api_get(
                f"/injuries?fixture={fixture_id}",
                use_cache=True, ttl=3600
            )
            if injuries:
                home_inj = sum(1 for p in injuries
                               if p.get("team", {}).get("id") == home_id
                               and p.get("player", {}).get("reason") in ("Injured","Suspended"))
                away_inj = sum(1 for p in injuries
                               if p.get("team", {}).get("id") == away_id
                               and p.get("player", {}).get("reason") in ("Injured","Suspended"))
                ctx["home_bajas"] = home_inj
                ctx["away_bajas"] = away_inj
        except Exception:
            pass

        # ── Head to head ─────────────────────────────────────────────
        if home_id and away_id:
            try:
                h2h = api_get(
                    f"/fixtures/headtohead?h2h={home_id}-{away_id}&last=5",
                    use_cache=True, ttl=7200
                )
                if h2h:
                    home_wins = sum(1 for m in h2h
                                    if m["teams"]["home"]["id"] == home_id
                                    and m["teams"]["home"]["winner"] is True)
                    away_wins = sum(1 for m in h2h
                                    if m["teams"]["away"]["id"] == away_id
                                    and m["teams"]["away"]["winner"] is True)
                    empates = len(h2h) - home_wins - away_wins
                    goles_h2h = [
                        (m["goals"]["home"] or 0) + (m["goals"]["away"] or 0)
                        for m in h2h
                    ]
                    ctx["h2h_home_wins"] = home_wins
                    ctx["h2h_away_wins"] = away_wins
                    ctx["h2h_empates"] = empates
                    ctx["h2h_goles_prom"] = round(sum(goles_h2h)/len(goles_h2h), 2) if goles_h2h else None
                    ctx["h2h_partidos"] = len(h2h)
            except Exception:
                pass

        # ── Prediccion API-Football ──────────────────────────────────
        try:
            pred = api_get(
                f"/predictions?fixture={fixture_id}",
                use_cache=True, ttl=3600
            )
            if pred:
                p0 = pred[0] if isinstance(pred, list) else pred
                ctx["api_prediccion_ganador"] = p0.get("predictions", {}).get("winner", {}).get("name")
                ctx["api_advice"] = p0.get("predictions", {}).get("advice")
                ctx["api_win_home_pct"] = p0.get("predictions", {}).get("percent", {}).get("home")
                ctx["api_win_away_pct"] = p0.get("predictions", {}).get("percent", {}).get("away")
                ctx["api_win_draw_pct"] = p0.get("predictions", {}).get("percent", {}).get("draws")
        except Exception:
            pass

        # ── Movimiento de cuotas ─────────────────────────────────────
        try:
            odds_hist = leer_json(ODDS_HISTORY_FILE)
            movs = [o for o in odds_hist
                    if str(o.get("fixture_id")) == str(fixture_id)]
            if len(movs) >= 2:
                primera = movs[0]
                ultima = movs[-1]
                ctx["odds_apertura_over25"] = primera.get("over25")
                ctx["odds_cierre_over25"] = ultima.get("over25")
                ctx["odds_mov_over25"] = round(
                    (ultima.get("over25") or 0) - (primera.get("over25") or 0), 3
                ) if primera.get("over25") and ultima.get("over25") else None
        except Exception:
            pass

    except Exception as e:
        ctx["error_enriquecimiento"] = str(e)

    return ctx



def _analizar_efectividad_por_minuto():
    """
    Lee aprendizaje.json y calcula la efectividad de picks live
    agrupados por rango de minuto (0-30, 31-60, 61-75, 76-90).
    Devuelve el mejor momento para analizar cada mercado.
    """
    datos = leer_json(APRENDIZAJE_FILE)
    live_cerrados = [
        d for d in datos
        if d.get("tipo") in ("pick_live_all",) or d.get("tipo_pick") == "live"
        if d.get("resultado") in ("acierto", "fallo")
        if d.get("minuto_consulta") is not None
    ]

    if len(live_cerrados) < 5:
        return None

    rangos = {
        "0-30": {"picks": [], "label": "Inicio (0-30min)"},
        "31-60": {"picks": [], "label": "Mitad (31-60min)"},
        "61-75": {"picks": [], "label": "Final (61-75min)"},
        "76-90": {"picks": [], "label": "Cierre (76-90min)"},
    }

    for d in live_cerrados:
        try:
            min_val = int(d.get("minuto_consulta", 0) or 0)
        except (ValueError, TypeError):
            continue
        if min_val <= 30:
            rangos["0-30"]["picks"].append(d)
        elif min_val <= 60:
            rangos["31-60"]["picks"].append(d)
        elif min_val <= 75:
            rangos["61-75"]["picks"].append(d)
        else:
            rangos["76-90"]["picks"].append(d)

    resultado = {}
    for rango, v in rangos.items():
        picks = v["picks"]
        if not picks:
            continue
        aciertos = sum(1 for p in picks if p.get("resultado") == "acierto")
        ef = round(aciertos / len(picks) * 100, 1)
        # Por mercado dentro del rango
        mercados = {}
        for p in picks:
            m = p.get("mercado", "Otro")
            if m not in mercados:
                mercados[m] = {"total": 0, "aciertos": 0}
            mercados[m]["total"] += 1
            if p.get("resultado") == "acierto":
                mercados[m]["aciertos"] += 1
        mejor_m = max(
            mercados.items(),
            key=lambda x: x[1]["aciertos"]/x[1]["total"] if x[1]["total"] else 0
        )[0] if mercados else None

        resultado[rango] = {
            "label": v["label"],
            "total": len(picks),
            "aciertos": aciertos,
            "efectividad": ef,
            "mejor_mercado": mejor_m,
            "mercados": {
                m: round(mv["aciertos"]/mv["total"]*100, 1)
                for m, mv in mercados.items() if mv["total"] >= 2
            }
        }

    # Mejor rango general
    mejor_rango = max(
        resultado.items(),
        key=lambda x: x[1]["efectividad"]
    )[0] if resultado else None

    return {"rangos": resultado, "mejor_rango": mejor_rango}

def _registrar_aprendizaje(pick, resultado):
    """
    Cada vez que un pick se cierra (acierto/fallo), extrae variables
    clave y las guarda en aprendizaje.json para analisis de tendencias.
    """
    partido = pick.get("partido", "")
    partes = partido.split(" vs ")
    home = partes[0].strip() if len(partes) == 2 else ""
    away = partes[1].strip() if len(partes) == 2 else ""

    # Contexto enriquecido via API
    fixture_id = pick.get("fixture_id")
    league_id  = pick.get("league_id")
    season     = pick.get("season")
    ctx = {}
    if fixture_id:
        try:
            ctx = _enriquecer_contexto_pick(fixture_id, league_id, season)
        except Exception:
            pass

    entrada = {
        # Identificacion
        "fecha": (pick.get("fecha_partido") or pick.get("fecha") or "")[:10],
        "fixture_id": fixture_id,
        "partido": partido,
        "home": home,
        "away": away,
        "liga": pick.get("league") or pick.get("liga") or "Desconocida",
        "pais": pick.get("country", ""),
        # Pick
        "mercado": pick.get("mercado", ""),
        "jugada": pick.get("jugada", ""),
        "score": float(pick.get("score", 0) or 0),
        "riesgo": float(pick.get("riesgo", 5) or 5),
        "probabilidad": float(pick.get("probabilidad", 0) or 0),
        "cuota": float(pick.get("cuota", 1.0) or 1.0),
        "tipo": pick.get("tipo", "prematch"),
        "minuto_consulta": pick.get("minuto_consulta"),  # para picks live
        "resultado": resultado,
        "timestamp_aprendizaje": fecha_hora_peru(),
        # Variables enriquecidas (todas las que pudo obtener la API)
        **ctx,
    }
    agregar_json(APRENDIZAJE_FILE, entrada)


def _analizar_tendencias_aprendizaje():
    """
    Lee aprendizaje.json y devuelve un dict con:
    - mercados mas confiables
    - ligas mas confiables
    - equipos con tendencias detectadas
    - rangos de score mas rentables
    - riesgo optimo
    """
    datos = leer_json(APRENDIZAJE_FILE)
    if not datos:
        return None

    cerrados = [d for d in datos if d.get("resultado") in ("acierto", "fallo")]
    if len(cerrados) < 5:
        return {"insuficiente": True, "total": len(cerrados)}

    def efectividad_grupo(items):
        if not items:
            return 0.0
        ac = sum(1 for i in items if i["resultado"] == "acierto")
        return round(ac / len(items) * 100, 1)

    mercados = {}
    for d in cerrados:
        m = d.get("mercado") or d.get("jugada", "Otro")
        if "Corner" in m:
            m = "Corners"
        elif "goles" in m.lower():
            m = "Goles"
        elif "Tarjeta" in m:
            m = "Tarjetas"
        elif "BTTS" in m or "Ambos" in m:
            m = "BTTS"
        else:
            m = "Otro"
        mercados.setdefault(m, []).append(d)

    mercados_ef = {m: {"efectividad": efectividad_grupo(v), "total": len(v)}
                   for m, v in mercados.items() if len(v) >= 3}

    ligas = {}
    for d in cerrados:
        lg = d.get("liga") or d.get("league") or "Desconocida"
        ligas.setdefault(lg, []).append(d)
    ligas_ef = {lg: {"efectividad": efectividad_grupo(v), "total": len(v)}
                for lg, v in ligas.items() if len(v) >= 3}

    equipos = {}
    for d in cerrados:
        for eq in [d.get("home", ""), d.get("away", "")]:
            if not eq:
                continue
            equipos.setdefault(eq, []).append(d)
    equipos_ef = {}
    for eq, items in equipos.items():
        if len(items) < 3:
            continue
        ef = efectividad_grupo(items)
        recientes = items[-3:]
        anteriores = items[:-3]
        ef_rec = efectividad_grupo(recientes) if recientes else ef
        ef_ant = efectividad_grupo(anteriores) if anteriores else ef
        tendencia = "mejorando" if ef_rec > ef_ant + 10 else "empeorando" if ef_rec < ef_ant - 10 else "estable"
        equipos_ef[eq] = {
            "efectividad": ef,
            "total": len(items),
            "tendencia": tendencia,
            "ef_reciente": ef_rec,
        }

    scores = {"7.5-8.4": [], "8.5-8.9": [], "9.0+": []}
    for d in cerrados:
        sc = float(d.get("score", 0) or 0)
        if sc >= 9.0:
            scores["9.0+"].append(d)
        elif sc >= 8.5:
            scores["8.5-8.9"].append(d)
        elif sc >= 7.5:
            scores["7.5-8.4"].append(d)
    scores_ef = {r: {"efectividad": efectividad_grupo(v), "total": len(v)}
                 for r, v in scores.items() if len(v) >= 2}

    riesgos = {"riesgo_1": [], "riesgo_2": [], "riesgo_3+": []}
    for d in cerrados:
        r = float(d.get("riesgo", 5) or 5)
        if r <= 1:
            riesgos["riesgo_1"].append(d)
        elif r <= 2:
            riesgos["riesgo_2"].append(d)
        else:
            riesgos["riesgo_3+"].append(d)
    riesgos_ef = {r: {"efectividad": efectividad_grupo(v), "total": len(v)}
                  for r, v in riesgos.items() if len(v) >= 2}

    mejor_mercado = max(mercados_ef.items(), key=lambda x: x[1]["efectividad"])[0] if mercados_ef else None
    mejor_liga = max(ligas_ef.items(), key=lambda x: x[1]["efectividad"])[0] if ligas_ef else None
    equipos_positivos = [
        eq for eq, v in equipos_ef.items()
        if v["tendencia"] == "mejorando" and v["efectividad"] >= 60
    ]

    return {
        "total_analizados": len(cerrados),
        "mercados": mercados_ef,
        "ligas": ligas_ef,
        "scores": scores_ef,
        "riesgos": riesgos_ef,
        "equipos": equipos_ef,
        "mejor_mercado": mejor_mercado,
        "mejor_liga": mejor_liga,
        "equipos_positivos": equipos_positivos[:5],
    }


def _guardar_snapshot_aprendizaje():
    """Guarda un snapshot de las tendencias actuales en feedback.json."""
    tendencias = _analizar_tendencias_aprendizaje()
    if not tendencias:
        return
    snapshot = {
        "tipo": "snapshot_aprendizaje",
        "fecha": fecha_hora_peru(),
        "resumen": tendencias,
    }
    agregar_json(FEEDBACK_FILE, snapshot)


# ─────────────────────────────────────────────
#  SISTEMA DE COMBINADAS
# ─────────────────────────────────────────────

def _cuota_segura(pick):
    """Extrae la cuota de un pick de forma segura, tolerando None, 0 y strings."""
    for campo in ("cuota", "cuota_minima"):
        val = pick.get(campo)
        if val is None:
            continue
        try:
            f = float(val)
            if f > 1.0:
                return f
        except (ValueError, TypeError):
            continue
    return 0.0


def _leer_bank_acumulado():
    """Lee el bank acumulado historico desde bank_acumulado.json."""
    try:
        data = leer_json(BANK_ACUMULADO_FILE)
        if isinstance(data, list) and data:
            return data
        return []
    except Exception:
        return []


def _guardar_bank_acumulado(entradas):
    """Guarda el historial del bank acumulado."""
    try:
        guardar_json_lista(BANK_ACUMULADO_FILE, entradas)
    except Exception:
        pass


def _actualizar_bank_acumulado():
    """
    Recorre todas las combinadas cerradas del mes actual y reconstruye
    el bank acumulado (S/500 al inicio del mes, stake 10%).
    Se reinicia a S/500 el primer dia de cada mes (a las 11:59 PM del ultimo dia).
    """
    try:
        combinadas = leer_json(COMBINADAS_FILE)
        hoy = fecha_hoy_peru()
        mes_actual = hoy[:7]  # YYYY-MM

        cerradas = [
            c for c in combinadas
            if c.get("estado","").lower() in ("acierto","fallo")
            and not c.get("sin_combinada")
            and c.get("fecha","")[:7] == mes_actual
        ]
        cerradas.sort(key=lambda c: c.get("timestamp", c.get("fecha","")))

        bank = BANK_INICIAL
        historial = [{
            "fecha": f"{mes_actual}-01",
            "bank": bank,
            "operacion": f"inicio_mes_{mes_actual}",
            "nota": f"Reinicio mensual — S/ {BANK_INICIAL:.2f}"
        }]

        for c in cerradas:
            stake = round(bank * STAKE_COMBINADA, 2)
            cuota = float(c.get("cuota_combinada", 1.0) or 1.0)
            estado = c.get("estado","").lower()
            subtipo = c.get("subtipo","?")
            ticket = c.get("ticket_id","")
            fecha = c.get("fecha","")

            if estado == "acierto":
                ganancia = round(stake * (cuota - 1), 2)
                bank = round(bank + ganancia, 2)
                op = f"+S/{ganancia:.2f}"
            else:
                bank = round(bank - stake, 2)
                op = f"-S/{stake:.2f}"

            historial.append({
                "fecha": fecha,
                "ticket": ticket,
                "subtipo": subtipo,
                "cuota": cuota,
                "estado": estado,
                "stake": stake,
                "operacion": op,
                "bank": bank,
                "mes": mes_actual,
            })

        _guardar_bank_acumulado(historial)
        return historial
    except Exception:
        return []


def _resetear_bank_acumulado_fin_mes():
    """
    Llamado a las 11:59 PM del ultimo dia del mes.
    Guarda el resultado final del mes y resetea el bank a S/500.
    """
    try:
        historial = _leer_bank_acumulado()
        if not historial:
            return

        bank_final = historial[-1].get("bank", BANK_INICIAL)
        resultado = round(bank_final - BANK_INICIAL, 2)
        roi = round(resultado / BANK_INICIAL * 100, 2)
        mes = fecha_hoy_peru()[:7]

        # Guardar resumen del mes en aprendizaje
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "cierre_mes_bank",
            "mes": mes,
            "bank_inicio": BANK_INICIAL,
            "bank_final": bank_final,
            "resultado": resultado,
            "roi": roi,
            "operaciones": len([h for h in historial if h.get("estado")]),
            "timestamp": fecha_hora_peru(),
        })

        # Resetear para el mes siguiente
        nuevo_historial = [{
            "fecha": fecha_hoy_peru(),
            "bank": BANK_INICIAL,
            "operacion": f"reinicio_inicio_mes",
            "nota": f"Cierre mes {mes}: S/{bank_final:.2f} ({roi:+.2f}%). Nuevo mes: S/{BANK_INICIAL:.2f}"
        }]
        _guardar_bank_acumulado(nuevo_historial)
    except Exception:
        pass


def _prob_recalibrada_pick(p):
    """
    Probabilidad recalibrada de un pick guardado. Si el pick ya fue
    recalibrado en origen, su 'probabilidad' ya es la corregida; si no,
    se recalibra aqui. Idempotente gracias a recalibrar_probabilidad.
    """
    if p.get("_recalibrado"):
        base = p.get("probabilidad", p.get("prob", 0))
    else:
        base = p.get("prob_original",
                      p.get("probabilidad", p.get("prob", 0)))
    return recalibrar_probabilidad(base)


def _score_recalibrado_pick(p):
    """Score recalibrado de un pick guardado (idempotente)."""
    if p.get("_recalibrado"):
        return float(p.get("score", 0) or 0)
    base = p.get("score_original", p.get("score", 0))
    liga = p.get("league", p.get("liga", ""))
    s = recalibrar_score(base) * multiplicador_liga(liga)
    return round(clamp(s, 0, 10), 1)


def _valor_combinada(picks_sel):
    """
    Valor de una combinada = VALOR ESPERADO REAL.
    VE = prob_conjunta * (cuota_comb - 1) - (1 - prob_conjunta)
    Usa la probabilidad RECALIBRADA de cada eslabon (no la declarada).
    VE > 0  -> combinada con valor positivo.
    VE <= 0 -> combinada sin valor (se descarta en el selector).
    """
    if not picks_sel:
        return -1.0
    cuota_comb = 1.0
    prob_conj = 1.0
    for p in picks_sel:
        cuota = max(_cuota_segura(p), 1.0)
        prob = _prob_recalibrada_pick(p) / 100.0
        cuota_comb *= cuota
        prob_conj *= prob
    ve = prob_conj * (cuota_comb - 1.0) - (1.0 - prob_conj)
    return round(ve, 4)


def _eslabon_valido_combinada(p):
    """
    True si un pick puede ser eslabon de combinada. Se evalua pick por
    pick (no por promedio): un solo eslabon debil invalida el ticket.
      - prob recalibrada >= COMB_PROB_MIN
      - score recalibrado >= COMB_SCORE_MIN (8.0 para Over 1.5)
      - cuota del eslabon >= CUOTA_MINIMA_ESLABON
      - no es BTTS
    """
    if _es_btts(p):
        return False
    cuota = _cuota_segura(p)
    if cuota < CUOTA_MINIMA_ESLABON:
        return False
    if _prob_recalibrada_pick(p) < COMB_PROB_MIN:
        return False
    score_rec = _score_recalibrado_pick(p)
    jugada = (p.get("jugada", "") or "").lower()
    if "over 1.5" in jugada:
        return score_rec >= COMB_SCORE_MIN_OVER15
    return score_rec >= COMB_SCORE_MIN


def _es_btts(pick):
    """Detecta si un pick es del mercado BTTS (Ambos Marcan)."""
    jugada = (pick.get("jugada","") or "").lower()
    mercado = (pick.get("mercado","") or "").lower()
    return (
        "ambos marcan" in jugada or
        "btts" in jugada or
        "btts" in mercado or
        "both teams" in mercado
    )


def _riesgo_ok(pick, riesgo_max=3):
    """
    Verifica si el pick cumple el criterio de riesgo.
    Excepcion: mercado de Tarjetas no tiene limite de riesgo
    porque su riesgo inherente es mas alto pero su efectividad es buena.
    """
    jugada = pick.get("jugada","").lower()
    mercado = pick.get("mercado","").lower()
    if "tarjeta" in jugada or "tarjeta" in mercado or "card" in mercado:
        return True  # Tarjetas: sin limite de riesgo
    riesgo = float(pick.get("riesgo", 10) or 10)
    return riesgo <= riesgo_max


def _fixture_ids_ya_usados(hoy):
    """
    Retorna el conjunto de fixture_ids que NO deben usarse en nuevas combinadas:
    - Picks con score < 9.0: solo pueden estar en un ticket por dia
    - Picks con score 9.0+: pueden repetirse EN OTROS tickets, PERO solo si
      el partido aun no ha empezado (prematch pendiente) o sigue en curso (live).
      Si el partido ya finalizo o ya empezo, se excluye igualmente.
    """
    usados = set()
    hora_actual = fecha_peru_obj().strftime("%H:%M")

    try:
        combinadas = leer_json(COMBINADAS_FILE)
        for c in combinadas:
            if c.get("fecha","")[:10] != hoy:
                continue
            if c.get("sin_combinada"):
                continue
            for p in c.get("picks", []):
                fid = str(p.get("fixture_id",""))
                if not fid:
                    continue

                score = float(p.get("score", 0) or 0)
                tipo = p.get("tipo", "prematch")
                estado = p.get("estado", "pendiente").lower()

                # Si el pick ya tiene resultado (cerrado) -> excluir siempre
                if estado in ("acierto", "fallo"):
                    usados.add(fid)
                    continue

                # Si es prematch y ya empezo o ya finalizo -> excluir
                if tipo == "prematch":
                    hora_pick = p.get("hora", p.get("hour", ""))
                    if hora_pick and hora_pick <= hora_actual:
                        usados.add(fid)
                        continue

                # Score < 9.0: excluir (solo puede estar en un ticket)
                if score < 9.0:
                    usados.add(fid)

                # Score >= 9.0 y partido aun pendiente: permitir en otros tickets

    except Exception:
        pass
    return usados


def _armar_combinada_del_dia():
    """
    Selector automatico de combinadas prematch.
    Cada eslabon se evalua individualmente (no por promedio): un solo
    pick debil invalida el ticket. Filtros por eslabon:
      - prob recalibrada >= 80%, score recalibrado >= 7.5 (8.0 para Over1.5)
      - cuota del eslabon >= 1.50, no BTTS
    Solo se arman combinadas con VALOR ESPERADO > 0 y cuota total 2.50-4.50.
    """
    from itertools import combinations as _comb

    picks = leer_json(PICKS_FILE)
    hoy = fecha_hoy_peru()
    ya_usados = _fixture_ids_ya_usados(hoy)

    # Tomar todos los picks prematch pendientes de hoy
    candidatos = []
    for p in picks:
        fecha_pick = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if fecha_pick != hoy:
            continue
        if p.get("tipo", "") != "prematch":
            continue
        if p.get("estado", "pendiente").lower() not in ("pendiente", "pendiente_manual"):
            continue
        cuota = _cuota_segura(p)
        if cuota <= 0:
            continue
        # Riesgo maximo 3 (excepcion: tarjetas)
        if not _riesgo_ok(p, riesgo_max=3):
            continue
        # No repetir partidos ya usados en otras combinadas del dia
        fid = str(p.get("fixture_id",""))
        if fid and fid in ya_usados:
            continue
        # Verificar que el partido aun no haya comenzado
        hora_pick = p.get("hora", p.get("hour", ""))
        if hora_pick:
            try:
                hora_actual = fecha_peru_obj().strftime("%H:%M")
                if hora_pick <= hora_actual:
                    continue
            except Exception:
                pass
        # Filtro por eslabon: prob/score recalibrados, cuota minima, no BTTS.
        # Reemplaza tanto la exclusion suelta de BTTS como la ausencia de
        # filtros de calidad por pick.
        if not _eslabon_valido_combinada(p):
            continue
        # Priorizar picks con edge positivo vs Pinnacle
        edge_p = p.get("edge")
        p2 = dict(p)
        p2["_tiene_edge"] = edge_p is not None and edge_p >= 0
        candidatos.append(p2)

    if not candidatos:
        return None

    # Ordenar: primero picks con edge positivo vs Pinnacle
    candidatos.sort(key=lambda x: (
        0 if x.get("_tiene_edge") else 1,
        -float(x.get("score", 0) or 0)
    ))

    mejor = None
    mejor_valor = 0.0   # solo aceptamos combinadas con VE > 0
    mejor_razon = ""

    # Evaluar todas las combinaciones de 2 y 3 picks
    for n in [3, 2]:
        if len(candidatos) < n:
            continue
        for grupo in _comb(candidatos, n):
            grupo = list(grupo)
            cuota_comb = 1.0
            for p in grupo:
                cuota_comb *= max(_cuota_segura(p), 1.0)
            cuota_comb = round(cuota_comb, 2)
            # Rango de cuota total aceptable.
            if cuota_comb < CUOTA_COMBINADA_MIN:
                continue
            if cuota_comb > CUOTA_COMBINADA_MAX:
                continue
            # Valor esperado real: solo combinadas con VE positivo.
            valor = _valor_combinada(grupo)
            if valor > mejor_valor:
                mejor_valor = valor
                mejor = grupo
                mejor_razon = (
                    f"{'Triple' if n==3 else 'Doble'} optima — "
                    f"cuota {cuota_comb}x | VE={valor}"
                )

    if not mejor:
        # Guardar en aprendizaje: no hubo combinada rentable
        motivo_sin = (
            f"Ninguna combinacion con VE>0 y cuota "
            f"{CUOTA_COMBINADA_MIN}-{CUOTA_COMBINADA_MAX}x "
            f"({len(candidatos)} candidatos validos)"
        )
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_combinada",
            "fecha": hoy,
            "motivo": motivo_sin,
            "candidatos": len(candidatos),
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "fecha": hoy, "motivo": motivo_sin}

    cuota_combinada = 1.0
    for p in mejor:
        cuota_combinada *= float(p.get("cuota", 0) or p.get("cuota_minima", 0) or 1.0)
    cuota_combinada = round(cuota_combinada, 2)

    scores = [float(p.get("score", 0) or 0) for p in mejor]
    riesgos = [float(p.get("riesgo", 0) or 0) for p in mejor]

    resultado = {
        "fecha": hoy,
        "picks": mejor,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "razon_seleccion": mejor_razon,
        "score_promedio": round(sum(scores)/len(scores), 2),
        "riesgo_promedio": round(sum(riesgos)/len(riesgos), 2),
        "estado": "pendiente",
        "timestamp": fecha_hora_peru(),
    }

    # Aprendizaje: registrar combinada generada
    agregar_json(APRENDIZAJE_FILE, {
        "tipo": "combinada_generada",
        "fecha": hoy,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "score_promedio": resultado["score_promedio"],
        "riesgo_promedio": resultado["riesgo_promedio"],
        "timestamp": fecha_hora_peru(),
    })

    return resultado


def _guardar_combinada(combinada):
    """Guarda la combinada en combinadas.json con ticket_id unico."""
    import uuid as _uuid
    combinadas = leer_json(COMBINADAS_FILE)

    # Asignar ticket_id unico si no tiene
    if not combinada.get("ticket_id"):
        subtipo = combinada.get("subtipo", "pre")[:3].upper()
        fecha_c = (combinada.get("fecha") or fecha_hoy_peru()).replace("-","")[2:]
        uid = str(_uuid.uuid4())[:6].upper()
        combinada["ticket_id"] = f"COMB-{subtipo}-{fecha_c}-{uid}"

    # Buscar por ticket_id exacto (actualizacion)
    for c in combinadas:
        if c.get("ticket_id") == combinada.get("ticket_id"):
            c.update(combinada)
            guardar_json_lista(COMBINADAS_FILE, combinadas)
            return

    combinadas.append(combinada)
    guardar_json_lista(COMBINADAS_FILE, combinadas)


# Chat IDs que reciben alarmas de combinadas
_CHAT_IDS_ALARMAS = set()

def _registrar_chat_alarma(chat_id):
    """Registra un chat_id para recibir alarmas de combinadas."""
    _CHAT_IDS_ALARMAS.add(str(chat_id))

def _actualizar_resultado_combinada():
    """
    Revisa combinadas pendientes, actualiza su resultado cuando
    todos los picks esten cerrados y registra aprendizaje de picks nuevos.
    """
    combinadas = leer_json(COMBINADAS_FILE)
    picks_todos = leer_json(PICKS_FILE)
    cambios = False

    for p in picks_todos:
        estado = p.get("estado", "").lower()
        if estado in ("acierto", "fallo") and not p.get("aprendizaje_registrado"):
            _registrar_aprendizaje(p, estado)
            p["aprendizaje_registrado"] = True
            cambios = True

    if cambios:
        guardar_json_lista(PICKS_FILE, picks_todos)

    # Indice por fixture_id y por partido+jugada
    idx_picks_fid = {}
    idx_picks_pj = {}  # partido+jugada -> pick
    for p in picks_todos:
        fid = str(p.get("fixture_id",""))
        if fid:
            idx_picks_fid[fid] = p
        clave_pj = f"{p.get('partido','')}|{p.get('jugada','')}"
        idx_picks_pj[clave_pj] = p

    for c in combinadas:
        if c.get("estado") != "pendiente":
            continue
        picks_c = c.get("picks", [])
        estados = []
        picks_actualizados = False

        for pick_c in picks_c:
            fid = str(pick_c.get("fixture_id", ""))
            jugada_comb = pick_c.get("jugada", "")
            partido_nombre = pick_c.get("partido", "")
            clave_pj = f"{partido_nombre}|{jugada_comb}"

            # Buscar en picks_guardados.json
            p_actual = idx_picks_fid.get(fid) or idx_picks_pj.get(clave_pj)

            if p_actual:
                estado_p = p_actual.get("estado", "pendiente").lower()
                # Actualizar estado dentro de la combinada si cambio
                if pick_c.get("estado","pendiente") != estado_p and estado_p in ("acierto","fallo"):
                    pick_c["estado"] = estado_p
                    pick_c["resultado_real"] = p_actual.get("resultado_real","")
                    picks_actualizados = True
            else:
                # Pick live: consultar API directamente para verificar resultado
                estado_p = pick_c.get("estado","pendiente").lower()
                if estado_p == "pendiente" and fid:
                    try:
                        fx = api_get(f"/fixtures?id={fid}", use_cache=False)
                        if fx:
                            status = fx[0]["fixture"]["status"]["short"]
                            if status in ("FT","AET","PEN"):
                                gh = fx[0]["goals"]["home"] or 0
                                ga = fx[0]["goals"]["away"] or 0
                                total = gh + ga

                                # Evaluar jugada
                                acierto = None
                                if "Under 3.5" in jugada_comb: acierto = total <= 3
                                elif "Over 2.5" in jugada_comb: acierto = total >= 3
                                elif "Over 1.5" in jugada_comb: acierto = total >= 2
                                elif "Ambos marcan" in jugada_comb: acierto = gh>0 and ga>0
                                elif "Corners Over" in jugada_comb:
                                    stats = api_get(f"/fixtures/statistics?fixture={fid}", use_cache=False)
                                    if stats:
                                        tc = 0
                                        for td in stats:
                                            for item in td.get("statistics",[]):
                                                if item.get("type")=="Corner Kicks":
                                                    try: tc += int(str(item.get("value") or 0).replace("%","").strip() or 0)
                                                    except: pass
                                        linea = float(''.join(c2 for c2 in jugada_comb.split("Over")[-1] if c2.isdigit() or c2=="."))
                                        acierto = tc > linea
                                        pick_c["resultado_real"] = f"{tc} corners"
                                elif "Tarjetas Over" in jugada_comb:
                                    stats = api_get(f"/fixtures/statistics?fixture={fid}", use_cache=False)
                                    if stats:
                                        tt = 0
                                        for td in stats:
                                            for item in td.get("statistics",[]):
                                                if item.get("type") in ("Yellow Cards","Red Cards"):
                                                    try:
                                                        v = int(str(item.get("value") or 0))
                                                        tt += v*2 if "Red" in item.get("type","") else v
                                                    except: pass
                                        linea = float(''.join(c2 for c2 in jugada_comb.split("Over")[-1] if c2.isdigit() or c2=="."))
                                        acierto = tt > linea
                                        pick_c["resultado_real"] = f"{tt} tarjetas"
                                elif "1X" in jugada_comb: acierto = gh >= ga
                                elif "X2" in jugada_comb: acierto = ga >= gh

                                if acierto is True:
                                    pick_c["estado"] = "acierto"
                                    if not pick_c.get("resultado_real"):
                                        pick_c["resultado_real"] = f"{gh}-{ga}"
                                    picks_actualizados = True
                                    estado_p = "acierto"
                                elif acierto is False:
                                    pick_c["estado"] = "fallo"
                                    if not pick_c.get("resultado_real"):
                                        pick_c["resultado_real"] = f"{gh}-{ga}"
                                    picks_actualizados = True
                                    estado_p = "fallo"
                    except Exception:
                        pass

            estados.append(estado_p)

        cerrados = [e for e in estados if e in ("acierto", "fallo")]
        if len(cerrados) == len(picks_c):
            if all(e == "acierto" for e in estados):
                c["estado"] = "acierto"
            elif any(e == "fallo" for e in estados):
                c["estado"] = "fallo"
                for i, e in enumerate(estados):
                    if e == "fallo":
                        c["fallo_en"] = picks_c[i].get("partido", "")
                        break

    guardar_json_lista(COMBINADAS_FILE, combinadas)

    # Registrar resultados cerrados en aprendizaje.json
    for c in combinadas:
        if c.get("estado") in ("acierto", "fallo") and not c.get("aprendizaje_registrado"):
            # Detectar patrones: que mercados, ligas, minutos funcionan
            picks_c = c.get("picks", [])
            mercados_c = [p.get("mercado","") for p in picks_c]
            ligas_c = [p.get("league","") or p.get("liga","") for p in picks_c]
            fuentes_c = [p.get("_fuente", p.get("tipo","prematch")) for p in picks_c]
            scores_c = [float(p.get("score",0) or 0) for p in picks_c]
            riesgos_c = [float(p.get("riesgo",0) or 0) for p in picks_c]
            cuotas_c = [_cuota_segura(p) for p in picks_c]

            agregar_json(APRENDIZAJE_FILE, {
                "tipo": "resultado_combinada",
                "ticket_id": c.get("ticket_id",""),
                "subtipo": c.get("subtipo","prematch"),
                "fecha": c.get("fecha",""),
                "estado": c.get("estado",""),
                "cuota_combinada": c.get("cuota_combinada"),
                "n_picks": c.get("n_picks", len(picks_c)),
                "score_promedio": c.get("score_promedio"),
                "riesgo_promedio": c.get("riesgo_promedio"),
                "valor_optimizacion": c.get("valor_optimizacion"),
                "mercados": mercados_c,
                "ligas": ligas_c,
                "fuentes": fuentes_c,
                "scores_individuales": scores_c,
                "riesgos_individuales": riesgos_c,
                "cuotas_individuales": cuotas_c,
                "fallo_en": c.get("fallo_en",""),
                "timestamp": fecha_hora_peru(),
                # Patrones detectables
                "todos_misma_liga": len(set(ligas_c)) == 1,
                "todos_mismo_mercado": len(set(mercados_c)) == 1,
                "mezcla_live_prematch": "live" in fuentes_c and "prematch" in fuentes_c,
                "score_min": min(scores_c) if scores_c else 0,
                "score_max": max(scores_c) if scores_c else 0,
                "cuota_min_pick": min(cuotas_c) if cuotas_c else 0,
            })
            c["aprendizaje_registrado"] = True

    guardar_json_lista(COMBINADAS_FILE, combinadas)


def _formato_combinada_telegram(combinada, bank_actual=None):
    """Formatea una combinada para mostrar en Telegram."""
    if not combinada:
        return "No hay combinada disponible para hoy (se necesitan picks score 8.0+ riesgo 2 cuota 1.30+)."

    # Sin combinada rentable
    if combinada.get("sin_combinada"):
        motivo = combinada.get("motivo", "")
        return (
            "\U0001f6ab *Sin combinada rentable hoy*\n"
            + motivo + "\n"
            + "El bot seguira monitoreando picks nuevos del dia."
        )

    bank = bank_actual or BANK_INICIAL
    stake = round(bank * STAKE_COMBINADA, 2)
    ganancia_pot = round(stake * (combinada["cuota_combinada"] - 1), 2)

    n = combinada.get("n_picks", len(combinada.get("picks", [])))
    tipo = "TRIPLE" if n == 3 else "DOBLE"

    ticket_id = combinada.get("ticket_id", "")
    lineas = [
        f"🎯 *COMBINADA {tipo} DEL DIA — {combinada['fecha']}*",
        f"🎟 Ticket: `{ticket_id}`" if ticket_id else "",
        f"📊 Score prom: {combinada.get('score_promedio','?')} | Riesgo prom: {combinada.get('riesgo_promedio','?')}",
        "━━━━━━━━━━",
    ]
    lineas = [l for l in lineas if l]  # quitar lineas vacias
    for i, p in enumerate(combinada["picks"], 1):
        cuota_p = _cuota_segura(p)
        minuto = p.get("minuto_consulta","")
        hora_str = f"Min:{minuto}'" if minuto else p.get("hora", p.get("hour",""))
        lineas.append(
            f"{i}. *{p.get('partido', '')}*\n"
            f"   \U0001f310 {p.get('country','')} | \U0001f3c6 {p.get('league','')} | \U0001f552 {hora_str}\n"
            f"   \U0001f3af {p.get('jugada', '')}\n"
            f"   Score: {p.get('score', '')} | Prob: {p.get('probabilidad',p.get('prob',''))}% | Cuota: {cuota_p if cuota_p else 'N/D'}"
        )
    lineas += [
        "━━━━━━━━━━",
        f"📊 Cuota combinada: *{combinada['cuota_combinada']}x*",
        f"💰 Stake sugerido (10% bank): *S/ {stake:.2f}*",
        f"📈 Ganancia potencial: *S/ {ganancia_pot:.2f}*",
        f"🧠 Optimizacion: {combinada.get('razon_seleccion','')}",
    ]
    return "\n".join(lineas)


async def combinada(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /combinada — muestra la mejor combinada del dia."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("Armando combinada del dia...")

    _actualizar_resultado_combinada()
    comb = _armar_combinada_del_dia()

    if comb and not comb.get("sin_combinada"):
        _guardar_combinada(comb)
        ticket = comb.get("ticket_id", "")
        await update.message.reply_text(
            f"✅ Combinada generada y guardada | Ticket: `{ticket}`",
            parse_mode="Markdown"
        )

    msg = _formato_combinada_telegram(comb)
    await update.message.reply_text(msg, parse_mode="Markdown")


def _calcular_rendimiento_mes(anio, mes):
    """
    Lee picks_guardados.json y calcula todas las metricas del mes indicado.
    Retorna un dict con los datos listos para el PDF y el snapshot de aprendizaje.
    """
    picks = leer_json(PICKS_FILE)
    hoy = fecha_peru_obj()

    picks_mes = []
    for p in picks:
        fecha_str = p.get("fecha_partido") or p.get("fecha") or ""
        try:
            fp = datetime.strptime(fecha_str[:10], "%Y-%m-%d")
            if fp.year == anio and fp.month == mes:
                picks_mes.append(p)
        except Exception:
            continue

    if not picks_mes:
        return None

    dias = {}
    for p in picks_mes:
        fecha_str = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if fecha_str not in dias:
            dias[fecha_str] = {"total": 0, "aciertos": 0, "fallos": 0, "pendientes": 0}
        estado = p.get("estado", "pendiente").lower()
        dias[fecha_str]["total"] += 1
        if estado == "acierto":
            dias[fecha_str]["aciertos"] += 1
        elif estado == "fallo":
            dias[fecha_str]["fallos"] += 1
        else:
            dias[fecha_str]["pendientes"] += 1

    dias_ord = sorted(dias.items())

    bank = BANK_INICIAL
    curva_bank = []
    picks_cerrados = [p for p in picks_mes if p.get("estado", "").lower() in ("acierto", "fallo")]
    picks_cerrados.sort(key=lambda p: (p.get("fecha_partido") or p.get("fecha") or ""))

    for p in picks_cerrados:
        score = float(p.get("score", 0) or 0)
        riesgo = float(p.get("riesgo", 10) or 10)
        cuota = float(p.get("cuota", 1.0) or 1.0)
        pct = _stake_pct(score, riesgo)
        stake = round(bank * pct, 2)
        if p.get("estado", "").lower() == "acierto":
            ganancia = round(stake * (cuota - 1), 2)
            bank = round(bank + ganancia, 2)
        else:
            bank = round(bank - stake, 2)
        fecha_str = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        curva_bank.append((fecha_str, round(bank, 2)))

    total = len(picks_mes)
    cerrados = [p for p in picks_mes if p.get("estado", "").lower() in ("acierto", "fallo")]
    aciertos = sum(1 for p in cerrados if p.get("estado", "").lower() == "acierto")
    fallos = len(cerrados) - aciertos
    pendientes = total - len(cerrados)
    efectividad = round((aciertos / len(cerrados) * 100), 1) if cerrados else 0.0

    cuotas_acierto = [float(p.get("cuota", 1.0) or 1.0) for p in cerrados if p.get("estado", "").lower() == "acierto"]
    cuota_prom = round(sum(cuotas_acierto) / len(cuotas_acierto), 2) if cuotas_acierto else 0.0
    roi = round(((bank - BANK_INICIAL) / BANK_INICIAL) * 100, 2)

    mercados = {}
    for p in cerrados:
        jugada = p.get("jugada", "Otro")
        if "Corner" in jugada:
            m = "Corners"
        elif "goles" in jugada.lower() or "gol" in jugada.lower():
            m = "Goles"
        elif "Tarjeta" in jugada:
            m = "Tarjetas"
        elif "BTTS" in jugada or "Ambos marcan" in jugada:
            m = "BTTS"
        elif "HT" in jugada:
            m = "HT Live"
        elif "1X" in jugada or "X2" in jugada or "12" in jugada:
            m = "Doble Oportunidad"
        else:
            m = "Otro"
        if m not in mercados:
            mercados[m] = {"total": 0, "aciertos": 0, "cuotas": []}
        mercados[m]["total"] += 1
        if p.get("estado", "").lower() == "acierto":
            mercados[m]["aciertos"] += 1
        mercados[m]["cuotas"].append(float(p.get("cuota", 1.0) or 1.0))

    mercados_stats = {}
    for m, v in mercados.items():
        ef = round(v["aciertos"] / v["total"] * 100, 1) if v["total"] else 0
        cq = round(sum(v["cuotas"]) / len(v["cuotas"]), 2) if v["cuotas"] else 0
        mercados_stats[m] = {
            "total": v["total"],
            "aciertos": v["aciertos"],
            "fallos": v["total"] - v["aciertos"],
            "efectividad": ef,
            "cuota_prom": cq
        }

    rangos_score = {
        "7.5-8.4": {"total": 0, "aciertos": 0},
        "8.5-8.9": {"total": 0, "aciertos": 0},
        "9.0+":    {"total": 0, "aciertos": 0},
    }
    for p in cerrados:
        sc = float(p.get("score", 0) or 0)
        if sc >= 9.0:
            r = "9.0+"
        elif sc >= 8.5:
            r = "8.5-8.9"
        elif sc >= 7.5:
            r = "7.5-8.4"
        else:
            continue
        rangos_score[r]["total"] += 1
        if p.get("estado", "").lower() == "acierto":
            rangos_score[r]["aciertos"] += 1

    score_stats = {}
    for r, v in rangos_score.items():
        ef = round(v["aciertos"] / v["total"] * 100, 1) if v["total"] else 0
        score_stats[r] = {"total": v["total"], "aciertos": v["aciertos"], "efectividad": ef}

    ligas = {}
    for p in cerrados:
        # Los picks guardan la liga como "league"; algunos reconstruidos
        # usan "liga". Se leen ambas claves para no caer todo en "Desconocida".
        liga = p.get("league") or p.get("liga") or "Desconocida"
        if liga not in ligas:
            ligas[liga] = {"total": 0, "aciertos": 0}
        ligas[liga]["total"] += 1
        if p.get("estado", "").lower() == "acierto":
            ligas[liga]["aciertos"] += 1

    liga_stats = {}
    for lg, v in ligas.items():
        ef = round(v["aciertos"] / v["total"] * 100, 1) if v["total"] else 0
        liga_stats[lg] = {"total": v["total"], "aciertos": v["aciertos"], "efectividad": ef}
    liga_stats = dict(sorted(liga_stats.items(), key=lambda x: x[1]["efectividad"], reverse=True))

    hoy_str = hoy.strftime("%Y-%m-%d")
    picks_hoy = [p for p in picks_mes if (p.get("fecha_partido") or p.get("fecha") or "")[:10] == hoy_str]
    cerrados_hoy = [p for p in picks_hoy if p.get("estado", "").lower() in ("acierto", "fallo")]
    aciertos_hoy = sum(1 for p in cerrados_hoy if p.get("estado", "").lower() == "acierto")
    fallos_hoy = len(cerrados_hoy) - aciertos_hoy
    ef_hoy = round(aciertos_hoy / len(cerrados_hoy) * 100, 1) if cerrados_hoy else None

    mejor_mercado_hoy = None
    if cerrados_hoy:
        mc = {}
        for p in cerrados_hoy:
            jugada = p.get("jugada", "Otro")
            if "Corner" in jugada:
                m = "Corners"
            elif "goles" in jugada.lower():
                m = "Goles"
            elif "Tarjeta" in jugada:
                m = "Tarjetas"
            else:
                m = "Otro"
            mc[m] = mc.get(m, 0) + (1 if p.get("estado", "").lower() == "acierto" else 0)
        if mc:
            mejor_mercado_hoy = max(mc, key=mc.get)

    return {
        "anio": anio,
        "mes": mes,
        "total": total,
        "cerrados": len(cerrados),
        "aciertos": aciertos,
        "fallos": fallos,
        "pendientes": pendientes,
        "efectividad": efectividad,
        "cuota_prom_aciertos": cuota_prom,
        "bank_inicial": BANK_INICIAL,
        "bank_final": round(bank, 2),
        "roi": roi,
        "curva_bank": curva_bank,
        "dias": dias_ord,
        "mercados": mercados_stats,
        "scores": score_stats,
        "ligas": liga_stats,
        "hoy": {
            "fecha": hoy_str,
            "total": len(picks_hoy),
            "cerrados": len(cerrados_hoy),
            "aciertos": aciertos_hoy,
            "fallos": fallos_hoy,
            "efectividad": ef_hoy,
            "mejor_mercado": mejor_mercado_hoy,
        }
    }


def _grafico_mercados_pie(picks, titulo="Efectividad por Mercado", path_out="temp_mercados.png"):
    """Grafico de torta: efectividad por mercado."""
    mercados = {}
    for p in picks:
        if p.get("estado","").lower() not in ("acierto","fallo"):
            continue
        jugada = p.get("jugada","Otro")
        if "Corner" in jugada: m = "Corners"
        elif "goles" in jugada.lower(): m = "Goles"
        elif "Tarjeta" in jugada: m = "Tarjetas"
        elif "BTTS" in jugada or "Ambos" in jugada: m = "BTTS"
        elif "1X" in jugada or "X2" in jugada: m = "Doble Oport."
        else: m = "Otro"
        if m not in mercados:
            mercados[m] = {"aciertos": 0, "fallos": 0}
        if p.get("estado","").lower() == "acierto":
            mercados[m]["aciertos"] += 1
        else:
            mercados[m]["fallos"] += 1

    if not mercados:
        return None

    labels = []
    sizes = []
    colores_pie = ["#27AE60","#2980B9","#E67E22","#8E44AD","#E74C3C","#1ABC9C"]
    for i,(m,v) in enumerate(mercados.items()):
        total = v["aciertos"] + v["fallos"]
        ef = round(v["aciertos"]/total*100,1) if total else 0
        labels.append(f"{m}\n{ef}% ({total})")
        sizes.append(total)

    fig, ax = plt.subplots(figsize=(7, 4))
    wedges, texts, autotexts = ax.pie(
        sizes, labels=labels, autopct="%1.0f%%",
        colors=colores_pie[:len(sizes)], startangle=90,
        textprops={"fontsize": 8}
    )
    for at in autotexts:
        at.set_fontsize(7)
    ax.set_title(titulo, fontsize=11, fontweight="bold")
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out


def _grafico_efectividad_periodo(picks, titulo="Efectividad por Dia", path_out="temp_ef_periodo.png"):
    """Grafico de barras: efectividad diaria del periodo."""
    dias = {}
    for p in picks:
        fecha = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if not fecha: continue
        estado = p.get("estado","").lower()
        if estado not in ("acierto","fallo"): continue
        if fecha not in dias:
            dias[fecha] = {"aciertos":0,"fallos":0}
        if estado == "acierto":
            dias[fecha]["aciertos"] += 1
        else:
            dias[fecha]["fallos"] += 1

    if not dias:
        return None

    fechas = sorted(dias.keys())
    efs = []
    labels = []
    for f in fechas:
        d = dias[f]
        cerr = d["aciertos"]+d["fallos"]
        efs.append(round(d["aciertos"]/cerr*100,1) if cerr else 0)
        labels.append(f[5:])  # MM-DD

    fig, ax = plt.subplots(figsize=(max(8, len(fechas)*0.6), 3.5))
    colores = ["#27AE60" if e >= 60 else "#E67E22" if e >= 40 else "#E74C3C" for e in efs]
    bars = ax.bar(range(len(efs)), efs, color=colores, alpha=0.85, width=0.6)
    ax.axhline(y=60, color="#2980B9", linestyle="--", linewidth=1.2, label="Meta 60%")
    ax.set_ylim(0, 110)
    ax.set_xticks(range(len(labels)))
    ax.set_xticklabels(labels, rotation=45, fontsize=7)
    ax.set_ylabel("Efectividad %", fontsize=9)
    ax.set_title(titulo, fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3, axis="y")
    # Valor encima de cada barra
    for bar, ef in zip(bars, efs):
        ax.text(bar.get_x()+bar.get_width()/2, bar.get_height()+1,
                f"{ef}%", ha="center", va="bottom", fontsize=7)
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out


def _grafico_prematch_vs_live(picks, path_out="temp_pvl.png"):
    """Grafico comparativo prematch vs live."""
    pre_a = sum(1 for p in picks if p.get("tipo","prematch")=="prematch" and p.get("estado","").lower()=="acierto")
    pre_f = sum(1 for p in picks if p.get("tipo","prematch")=="prematch" and p.get("estado","").lower()=="fallo")
    liv_a = sum(1 for p in picks if p.get("tipo","")=="live" and p.get("estado","").lower()=="acierto")
    liv_f = sum(1 for p in picks if p.get("tipo","")=="live" and p.get("estado","").lower()=="fallo")

    if (pre_a+pre_f+liv_a+liv_f) == 0:
        return None

    fig, axes = plt.subplots(1, 2, figsize=(8, 3.5))

    for ax, aciertos, fallos, label in [
        (axes[0], pre_a, pre_f, "Prematch"),
        (axes[1], liv_a, liv_f, "Live")
    ]:
        total = aciertos + fallos
        if total == 0:
            ax.text(0.5, 0.5, "Sin datos", ha="center", va="center", fontsize=10)
            ax.set_title(label, fontsize=10, fontweight="bold")
            continue
        ef = round(aciertos/total*100,1)
        colores = ["#27AE60","#E74C3C"]
        wedges, texts, autotexts = ax.pie(
            [aciertos, fallos],
            labels=[f"Aciertos\n{aciertos}", f"Fallos\n{fallos}"],
            autopct="%1.0f%%",
            colors=colores,
            startangle=90,
            textprops={"fontsize":8}
        )
        for at in autotexts:
            at.set_fontsize(8)
        ax.set_title(f"{label}\n{ef}% efectividad ({total} picks)", fontsize=9, fontweight="bold")

    fig.suptitle("Prematch vs Live", fontsize=11, fontweight="bold")
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out


def _grafico_scores_distribucion(picks, path_out="temp_scores.png"):
    """Histograma de distribucion de scores."""
    scores = [float(p.get("score",0) or 0) for p in picks
              if p.get("estado","").lower() in ("acierto","fallo")]
    aciertos_scores = [float(p.get("score",0) or 0) for p in picks
                       if p.get("estado","").lower()=="acierto"]
    fallos_scores = [float(p.get("score",0) or 0) for p in picks
                     if p.get("estado","").lower()=="fallo"]

    if not scores:
        return None

    fig, ax = plt.subplots(figsize=(8, 3.5))
    bins = [7.0, 7.5, 8.0, 8.5, 9.0, 9.5, 10.1]
    ax.hist(aciertos_scores, bins=bins, alpha=0.7, color="#27AE60",
            label=f"Aciertos ({len(aciertos_scores)})", width=0.2)
    ax.hist(fallos_scores, bins=bins, alpha=0.7, color="#E74C3C",
            label=f"Fallos ({len(fallos_scores)})", width=0.2,
            bottom=[0]*len(bins[:-1]))
    ax.axvline(x=9.0, color="#8E44AD", linestyle="--", linewidth=1.5, label="Umbral Elite")
    ax.axvline(x=8.5, color="#E67E22", linestyle="--", linewidth=1, label="Umbral TOP+")
    ax.set_xlabel("Score", fontsize=9)
    ax.set_ylabel("Picks", fontsize=9)
    ax.set_title("Distribucion de Scores — Aciertos vs Fallos", fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3, axis="y")
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out


def _insertar_graficos_pdf(elements, picks, prefijo="reporte", styles=None):
    """
    Genera e inserta graficos matplotlib en el PDF.
    Llama a todas las funciones de graficos y las agrega al story.
    """
    from reportlab.platypus import Image as RLImage
    from reportlab.lib.units import cm as _cm

    if styles is None:
        from reportlab.lib.styles import getSampleStyleSheet
        styles = getSampleStyleSheet()

    s_h2 = styles["Heading2"].clone("gh2")
    s_h2.fontSize = 11
    s_h2.textColor = colors.HexColor("#1A1A2E")
    s_h2.spaceBefore = 10
    s_h2.spaceAfter = 4

    tmps = []

    def add_graph(gen_fn, seccion_titulo, width, height, **kwargs):
        """Genera un grafico y lo agrega al PDF de forma segura.

        'seccion_titulo' es el encabezado de la seccion en el PDF.
        Se renombro desde 'titulo' para evitar colision con el argumento
        'titulo' que algunas funciones de grafico reciben via **kwargs.
        """
        try:
            path = gen_fn(**kwargs)
            if not path:
                return
            # Verificar que el archivo existe y tiene contenido
            if not _os_bot.path.exists(path) or _os_bot.path.getsize(path) == 0:
                return
            elements.append(Paragraph(seccion_titulo, s_h2))
            elements.append(RLImage(path, width=width*_cm, height=height*_cm))
            elements.append(Spacer(1, 0.3*_cm))
            tmps.append(path)
        except Exception as e:
            pass  # Grafico falla silenciosamente, el PDF sigue generandose

    add_graph(
        _grafico_efectividad_periodo,
        "Grafico: Efectividad por Dia",
        16, 5,
        picks=picks,
        titulo="Efectividad por Dia del Periodo",
        path_out=_tmp_path(f"tmp_{prefijo}_ef.png")
    )
    add_graph(
        _grafico_prematch_vs_live,
        "Grafico: Prematch vs Live",
        14, 5,
        picks=picks,
        path_out=_tmp_path(f"tmp_{prefijo}_pvl.png")
    )
    add_graph(
        _grafico_scores_distribucion,
        "Grafico: Distribucion de Scores",
        14, 5,
        picks=picks,
        path_out=_tmp_path(f"tmp_{prefijo}_sc.png")
    )
    add_graph(
        _grafico_mercados_pie,
        "Grafico: Distribucion de Mercados",
        12, 6,
        picks=picks,
        titulo="Participacion por Mercado",
        path_out=_tmp_path(f"tmp_{prefijo}_merc.png")
    )

    return tmps


def _generar_grafico_bank(curva_bank, anio, mes):
    """Genera grafico de evolucion del bank."""
    if not curva_bank:
        return None
    fechas = [c[0][5:] for c in curva_bank]
    valores = [c[1] for c in curva_bank]
    fig, ax = plt.subplots(figsize=(9, 3))
    color = "#27AE60" if valores[-1] >= BANK_INICIAL else "#E74C3C"
    ax.plot(range(len(valores)), valores, color=color, linewidth=2, marker="o", markersize=4)
    ax.axhline(y=BANK_INICIAL, color="#95A5A6", linestyle="--", linewidth=1, label=f"Bank inicial S/ {BANK_INICIAL}")
    ax.fill_between(range(len(valores)), BANK_INICIAL, valores,
                    where=[v >= BANK_INICIAL for v in valores], alpha=0.15, color="#27AE60")
    ax.fill_between(range(len(valores)), BANK_INICIAL, valores,
                    where=[v < BANK_INICIAL for v in valores], alpha=0.15, color="#E74C3C")
    ax.set_xticks(range(len(fechas)))
    ax.set_xticklabels(fechas, rotation=45, fontsize=7)
    ax.set_ylabel("Soles (S/)", fontsize=9)
    ax.set_title(f"Evolucion del Bank — {mes:02d}/{anio}", fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    path = _tmp_path(f"temp_bank_{anio}_{mes:02d}.png")
    fig.savefig(path, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path


def _generar_grafico_efectividad(dias, anio, mes):
    """Genera grafico de efectividad diaria."""
    fechas = []
    efectividades = []
    for fecha, d in dias:
        cerr = d["aciertos"] + d["fallos"]
        if cerr > 0:
            fechas.append(fecha[5:])
            efectividades.append(round(d["aciertos"] / cerr * 100, 1))
    if not efectividades:
        return None
    fig, ax = plt.subplots(figsize=(9, 3))
    colores = ["#27AE60" if e >= 60 else "#E67E22" if e >= 40 else "#E74C3C" for e in efectividades]
    ax.bar(range(len(efectividades)), efectividades, color=colores, alpha=0.85)
    ax.axhline(y=60, color="#2980B9", linestyle="--", linewidth=1, label="Meta 60%")
    ax.set_ylim(0, 105)
    ax.set_xticks(range(len(fechas)))
    ax.set_xticklabels(fechas, rotation=45, fontsize=7)
    ax.set_ylabel("Efectividad %", fontsize=9)
    ax.set_title(f"Efectividad Diaria — {mes:02d}/{anio}", fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3, axis="y")
    fig.tight_layout()
    path = _tmp_path(f"temp_efect_{anio}_{mes:02d}.png")
    fig.savefig(path, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path



def _grafico_tendencia_efectividad(dias, anio, mes, path_out=None):
    """
    Grafico de linea de tendencia de efectividad acumulada dia a dia.
    Muestra si la efectividad va mejorando o empeorando con el tiempo.
    """
    if not dias:
        return None
    path_out = path_out or _tmp_path(f"temp_tend_{anio}_{mes:02d}.png")

    fechas = []
    ef_acum = []
    acum_a, acum_f = 0, 0

    for fecha, d in dias:
        acum_a += d["aciertos"]
        acum_f += d["fallos"]
        cerr = acum_a + acum_f
        if cerr > 0:
            fechas.append(fecha[5:])
            ef_acum.append(round(acum_a / cerr * 100, 1))

    if len(ef_acum) < 2:
        return None

    # Calcular linea de tendencia (regresion lineal simple)
    n = len(ef_acum)
    x = list(range(n))
    x_mean = sum(x) / n
    y_mean = sum(ef_acum) / n
    num = sum((x[i] - x_mean) * (ef_acum[i] - y_mean) for i in range(n))
    den = sum((x[i] - x_mean) ** 2 for i in range(n))
    slope = num / den if den != 0 else 0
    intercept = y_mean - slope * x_mean
    tendencia = [intercept + slope * i for i in x]

    # Color segun tendencia
    color_tend = "#27AE60" if slope > 0 else "#E74C3C"
    tend_label = f"Tendencia ({'mejorando' if slope > 0 else 'bajando'}, {slope:+.2f}%/dia)"

    fig, ax = plt.subplots(figsize=(10, 4))
    ax.plot(range(n), ef_acum, color="#2980B9", linewidth=2.5,
            marker="o", markersize=5, label="Efectividad acumulada")
    ax.plot(range(n), tendencia, color=color_tend, linewidth=2,
            linestyle="--", label=tend_label)
    ax.axhline(y=60, color="#95A5A6", linestyle=":", linewidth=1, label="Meta 60%")
    ax.fill_between(range(n), ef_acum, 60,
                    where=[e >= 60 for e in ef_acum], alpha=0.1, color="#27AE60")
    ax.fill_between(range(n), ef_acum, 60,
                    where=[e < 60 for e in ef_acum], alpha=0.1, color="#E74C3C")
    ax.set_ylim(0, 105)
    ax.set_xticks(range(n))
    ax.set_xticklabels(fechas, rotation=45, fontsize=7)
    ax.set_ylabel("Efectividad % (acumulada)", fontsize=9)
    ax.set_title(f"Tendencia de Efectividad — {mes:02d}/{anio}", fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out if _os_bot.path.exists(path_out) else None


def _grafico_bank_acumulado(historial, path_out=None):
    """
    Grafico de evolucion del bank acumulado desde el inicio.
    Muestra las dos lineas: bank diario (reinicio S/500) vs acumulado.
    """
    if not historial or len(historial) < 2:
        return None
    path_out = path_out or _tmp_path("temp_bank_acum.png")

    fechas = [h.get("fecha","") for h in historial]
    valores = [h.get("bank", 500.0) for h in historial]
    colores_pts = []
    for h in historial:
        if h.get("operacion") == "inicio":
            colores_pts.append("#888780")
        elif h.get("estado") == "acierto":
            colores_pts.append("#27AE60")
        else:
            colores_pts.append("#E74C3C")

    fig, ax = plt.subplots(figsize=(12, 4))
    color_line = "#27AE60" if valores[-1] >= BANK_INICIAL else "#E74C3C"
    ax.plot(range(len(valores)), valores, color=color_line,
            linewidth=2.5, marker="o", markersize=5)
    # Color each point
    for i, (v, col) in enumerate(zip(valores, colores_pts)):
        ax.plot(i, v, "o", color=col, markersize=6, zorder=5)

    ax.axhline(y=BANK_INICIAL, color="#95A5A6", linestyle="--",
               linewidth=1.5, label=f"Bank inicial S/ {BANK_INICIAL:.0f}")
    ax.fill_between(range(len(valores)), BANK_INICIAL, valores,
                    where=[v >= BANK_INICIAL for v in valores],
                    alpha=0.12, color="#27AE60")
    ax.fill_between(range(len(valores)), BANK_INICIAL, valores,
                    where=[v < BANK_INICIAL for v in valores],
                    alpha=0.12, color="#E74C3C")

    # Labels cada 5 operaciones
    ticks = list(range(0, len(fechas), max(1, len(fechas)//10)))
    ax.set_xticks(ticks)
    ax.set_xticklabels([fechas[i][5:] if i < len(fechas) else "" for i in ticks],
                        rotation=45, fontsize=7)
    ax.set_ylabel("Soles (S/)", fontsize=9)
    resultado = valores[-1] - BANK_INICIAL
    titulo_r = f"+S/ {resultado:.2f}" if resultado >= 0 else f"-S/ {abs(resultado):.2f}"
    ax.set_title(f"Bank Acumulado desde inicio (S/ {BANK_INICIAL:.0f}) — {titulo_r}",
                 fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out if _os_bot.path.exists(path_out) else None


def _grafico_bank_combinadas(combinadas_mes, bank_inicial=500.0, path_out=None):
    """
    Simula la evolucion del bank apostando solo en combinadas.
    Stake fijo 3% del bank por combinada.
    """
    if not combinadas_mes:
        return None
    path_out = path_out or _tmp_path("temp_bank_comb.png")

    cerradas = [c for c in combinadas_mes
                if c.get("estado","").lower() in ("acierto","fallo")
                and not c.get("sin_combinada")]
    if not cerradas:
        return None

    cerradas_ord = sorted(cerradas, key=lambda c: c.get("fecha",""))
    bank = bank_inicial
    fechas = ["inicio"]
    valores = [bank_inicial]

    for c in cerradas_ord:
        stake = round(bank * STAKE_COMBINADA, 2)
        cuota = float(c.get("cuota_combinada", 1.0) or 1.0)
        if c.get("estado","").lower() == "acierto":
            bank = round(bank + stake * (cuota - 1), 2)
        else:
            bank = round(bank - stake, 2)
        fechas.append(c.get("fecha","")[5:])
        valores.append(bank)

    if len(valores) < 2:
        return None

    fig, ax = plt.subplots(figsize=(10, 4))
    color = "#27AE60" if valores[-1] >= bank_inicial else "#E74C3C"
    ax.plot(range(len(valores)), valores, color=color, linewidth=2.5,
            marker="o", markersize=5)
    ax.axhline(y=bank_inicial, color="#95A5A6", linestyle="--",
               linewidth=1.5, label=f"Bank inicial S/ {bank_inicial:.0f}")
    ax.fill_between(range(len(valores)), bank_inicial, valores,
                    where=[v >= bank_inicial for v in valores],
                    alpha=0.15, color="#27AE60")
    ax.fill_between(range(len(valores)), bank_inicial, valores,
                    where=[v < bank_inicial for v in valores],
                    alpha=0.15, color="#E74C3C")
    ax.set_xticks(range(len(fechas)))
    ax.set_xticklabels(fechas, rotation=45, fontsize=7)
    ax.set_ylabel("Soles (S/)", fontsize=9)
    resultado = valores[-1] - bank_inicial
    titulo_r = f"+S/ {resultado:.2f}" if resultado >= 0 else f"-S/ {abs(resultado):.2f}"
    ax.set_title(f"Bank Combinadas (S/ {bank_inicial:.0f} inicial) — {titulo_r}",
                 fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out if _os_bot.path.exists(path_out) else None


def _grafico_tendencia_combinadas(combinadas_mes, path_out=None):
    """
    Efectividad acumulada de combinadas con linea de tendencia.
    """
    if not combinadas_mes:
        return None
    path_out = path_out or _tmp_path("temp_tend_comb.png")

    cerradas = [c for c in sorted(combinadas_mes, key=lambda c: c.get("fecha",""))
                if c.get("estado","").lower() in ("acierto","fallo")
                and not c.get("sin_combinada")]
    if len(cerradas) < 2:
        return None

    acum_a, acum_f = 0, 0
    fechas = []
    ef_acum = []
    for c in cerradas:
        if c.get("estado","").lower() == "acierto":
            acum_a += 1
        else:
            acum_f += 1
        cerr = acum_a + acum_f
        fechas.append(c.get("fecha","")[5:])
        ef_acum.append(round(acum_a / cerr * 100, 1))

    n = len(ef_acum)
    x = list(range(n))
    x_mean = sum(x) / n
    y_mean = sum(ef_acum) / n
    num = sum((x[i]-x_mean)*(ef_acum[i]-y_mean) for i in range(n))
    den = sum((x[i]-x_mean)**2 for i in range(n))
    slope = num/den if den != 0 else 0
    intercept = y_mean - slope * x_mean
    tendencia = [intercept + slope * i for i in x]

    color_tend = "#27AE60" if slope > 0 else "#E74C3C"
    tend_label = f"Tendencia ({'mejorando' if slope > 0 else 'bajando'}, {slope:+.2f}%/comb)"

    fig, ax = plt.subplots(figsize=(10, 4))
    ax.plot(range(n), ef_acum, color="#8E44AD", linewidth=2.5,
            marker="o", markersize=5, label="Efectividad combinadas")
    ax.plot(range(n), tendencia, color=color_tend, linewidth=2,
            linestyle="--", label=tend_label)
    ax.axhline(y=55, color="#95A5A6", linestyle=":", linewidth=1, label="Meta 55%")
    ax.set_ylim(0, 110)
    ax.set_xticks(range(n))
    ax.set_xticklabels(fechas, rotation=45, fontsize=7)
    ax.set_ylabel("Efectividad % (acumulada)", fontsize=9)
    ax.set_title("Tendencia de Efectividad — Combinadas", fontsize=11, fontweight="bold")
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(path_out, dpi=120, bbox_inches="tight")
    plt.close(fig)
    return path_out if _os_bot.path.exists(path_out) else None

def generar_pdf_rendimiento(datos):
    """Genera el PDF completo de rendimiento mensual."""
    from reportlab.platypus import Image as RLImage
    from reportlab.lib.units import cm

    anio = datos["anio"]
    mes = datos["mes"]
    nombre_mes = ["", "Enero","Febrero","Marzo","Abril","Mayo","Junio",
                  "Julio","Agosto","Septiembre","Octubre","Noviembre","Diciembre"][mes]

    pdf_path = _tmp_path(f"rendimiento_{anio}_{mes:02d}.pdf")
    doc = SimpleDocTemplate(pdf_path, pagesize=A4,
                            leftMargin=1.5*cm, rightMargin=1.5*cm,
                            topMargin=1.5*cm, bottomMargin=1.5*cm)
    styles = getSampleStyleSheet()
    story = []
    # PUNTO 2 FIX: lista de PNG temporales a borrar DESPUES de doc.build()
    _tmps_pendientes = []

    def titulo(txt, size=14):
        s = styles["Heading1"].clone("t")
        s.fontSize = size
        s.textColor = colors.HexColor("#1A1A2E")
        s.spaceAfter = 6
        return Paragraph(txt, s)

    def subtitulo(txt):
        s = styles["Heading2"].clone("st")
        s.fontSize = 11
        s.textColor = colors.HexColor("#16213E")
        s.spaceBefore = 10
        s.spaceAfter = 4
        return Paragraph(txt, s)

    def tabla(data, col_widths=None):
        t = Table(data, colWidths=col_widths, repeatRows=1)
        t.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1A1A2E")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
            ("FONTSIZE", (0, 0), (-1, -1), 9),
            ("ALIGN", (0, 0), (-1, -1), "CENTER"),
            ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.HexColor("#F8F9FA"), colors.white]),
            ("GRID", (0, 0), (-1, -1), 0.4, colors.HexColor("#DEE2E6")),
            ("TOPPADDING", (0, 0), (-1, -1), 4),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        ]))
        return t

    story.append(Spacer(1, 0.5*cm))
    story.append(titulo(f"HarryNine V14 — Reporte de Rendimiento", size=16))
    story.append(titulo(f"{nombre_mes} {anio}  |  Al {datos['hoy']['fecha']}", size=12))
    story.append(Spacer(1, 0.3*cm))

    story.append(subtitulo("1. Resumen General del Mes"))
    lucro = round(datos["bank_final"] - BANK_INICIAL, 2)
    roi_txt = f"+{datos['roi']}%" if datos["roi"] >= 0 else f"{datos['roi']}%"
    lucro_txt = f"+S/ {lucro}" if lucro >= 0 else f"-S/ {abs(lucro)}"
    data_resumen = [
        ["Metrica", "Valor"],
        ["Total Picks analizados", str(datos["total"])],
        ["Picks cerrados", str(datos["cerrados"])],
        ["Aciertos", str(datos["aciertos"])],
        ["Fallos", str(datos["fallos"])],
        ["Pendientes", str(datos["pendientes"])],
        ["Efectividad global", f"{datos['efectividad']}%"],
        ["Cuota promedio (aciertos)", str(datos["cuota_prom_aciertos"])],
        ["Bank inicial", f"S/ {datos['bank_inicial']:.2f}"],
        ["Bank actual simulado", f"S/ {datos['bank_final']:.2f}"],
        ["Lucro / Perdida", lucro_txt],
        ["ROI estimado", roi_txt],
    ]
    story.append(tabla(data_resumen, col_widths=[9*cm, 5*cm]))
    story.append(Spacer(1, 0.3*cm))

    try:
        img_bank = _generar_grafico_bank(datos["curva_bank"], anio, mes)
        if img_bank and _os_bot.path.exists(img_bank) and _os_bot.path.getsize(img_bank) > 0:
            story.append(subtitulo("2. Evolucion del Bank (S/ 500 inicial)"))
            story.append(RLImage(img_bank, width=16*cm, height=5.5*cm))
            story.append(Spacer(1, 0.3*cm))
    except Exception:
        pass

    try:
        img_ef = _generar_grafico_efectividad(datos["dias"], anio, mes)
        if img_ef and _os_bot.path.exists(img_ef) and _os_bot.path.getsize(img_ef) > 0:
            story.append(subtitulo("3. Efectividad Diaria"))
            story.append(RLImage(img_ef, width=16*cm, height=5.5*cm))
            story.append(Spacer(1, 0.3*cm))
    except Exception:
        pass

    story.append(subtitulo("4. Detalle Dia a Dia"))
    data_dias = [["Fecha", "Total", "Aciertos", "Fallos", "Pend.", "Efectividad"]]
    for fecha, d in datos["dias"]:
        cerr = d["aciertos"] + d["fallos"]
        ef = f"{round(d['aciertos']/cerr*100,1)}%" if cerr else "--"
        data_dias.append([fecha[5:], str(d["total"]), str(d["aciertos"]),
                          str(d["fallos"]), str(d["pendientes"]), ef])
    acum_a = sum(d["aciertos"] for _, d in datos["dias"])
    acum_f = sum(d["fallos"] for _, d in datos["dias"])
    cerr_tot = acum_a + acum_f
    ef_tot = f"{round(acum_a/cerr_tot*100,1)}%" if cerr_tot else "--"
    data_dias.append(["TOTAL", str(datos["total"]), str(acum_a), str(acum_f),
                      str(datos["pendientes"]), ef_tot])
    story.append(tabla(data_dias, col_widths=[2.5*cm, 2*cm, 2.5*cm, 2*cm, 2*cm, 3*cm]))
    story.append(Spacer(1, 0.3*cm))

    story.append(subtitulo("5. Rendimiento por Mercado"))
    data_merc = [["Mercado", "Total", "Aciert.", "Fallos", "Efectiv.", "Cuota prom."]]
    for m, v in sorted(datos["mercados"].items(), key=lambda x: x[1]["efectividad"], reverse=True):
        data_merc.append([m, str(v["total"]), str(v["aciertos"]), str(v["fallos"]),
                          f"{v['efectividad']}%", str(v["cuota_prom"])])
    story.append(tabla(data_merc, col_widths=[4*cm, 2*cm, 2*cm, 2*cm, 2.5*cm, 3*cm]))
    story.append(Spacer(1, 0.3*cm))

    story.append(subtitulo("6. Rendimiento por Score"))
    data_sc = [["Rango Score", "Total", "Aciertos", "Efectividad", "Stake %"]]
    stake_map = {"7.5-8.4": "2%", "8.5-8.9": "3%", "9.0+": "5%"}
    for r, v in datos["scores"].items():
        data_sc.append([r, str(v["total"]), str(v["aciertos"]),
                        f"{v['efectividad']}%", stake_map.get(r, "--")])
    story.append(tabla(data_sc, col_widths=[4*cm, 2.5*cm, 3*cm, 3*cm, 2.5*cm]))
    story.append(Spacer(1, 0.3*cm))

    story.append(subtitulo("7. Rendimiento por Liga"))
    data_liga = [["Liga", "Total", "Aciertos", "Fallos", "Efectividad"]]
    for lg, v in datos["ligas"].items():
        data_liga.append([lg, str(v["total"]), str(v["aciertos"]),
                          str(v["total"]-v["aciertos"]), f"{v['efectividad']}%"])
    story.append(tabla(data_liga, col_widths=[6*cm, 2*cm, 2.5*cm, 2*cm, 2.5*cm]))
    story.append(Spacer(1, 0.3*cm))

    story.append(subtitulo(f"8. Resumen de Hoy — {datos['hoy']['fecha']}"))
    h = datos["hoy"]
    ef_hoy_txt = f"{h['efectividad']}%" if h["efectividad"] is not None else "Sin cerrados"
    data_hoy = [
        ["Metrica", "Valor"],
        ["Picks del dia", str(h["total"])],
        ["Cerrados hoy", str(h["cerrados"])],
        ["Aciertos hoy", str(h["aciertos"])],
        ["Fallos hoy", str(h["fallos"])],
        ["Efectividad hoy", ef_hoy_txt],
        ["Mejor mercado hoy", h["mejor_mercado"] or "--"],
    ]
    story.append(tabla(data_hoy, col_widths=[9*cm, 5*cm]))
    story.append(Spacer(1, 0.3*cm))

    # ── EFECTIVIDAD ANCLAS ───────────────────────────────────────────
    # ── ANALISIS DE EDGE VS PINNACLE ─────────────────────────────────
    story.append(subtitulo("9. Analisis de Valor vs Pinnacle (Edge)"))
    try:
        picks_con_edge = [p for p in picks_rend_all
                         if (p.get("fecha_partido") or p.get("fecha",""))[:7] == f"{anio}-{mes:02d}"
                         and p.get("edge") is not None
                         and p.get("estado","").lower() in ("acierto","fallo")]

        if picks_con_edge:
            # Agrupar por categoria de edge
            cats = {"EXCELENTE": [], "BUENO": [], "LEVE": [], "NEUTRO": [], "SIN VALOR": []}
            for p in picks_con_edge:
                cat = p.get("edge_categoria","SIN VALOR") or "SIN VALOR"
                if cat in cats:
                    cats[cat].append(p)

            data_edge = [["Categoria Edge", "Total", "Aciertos", "Efectividad", "ROI est."]]
            for cat, picks_cat in cats.items():
                if not picks_cat:
                    continue
                ac = sum(1 for p in picks_cat if p.get("estado","").lower()=="acierto")
                ef = round(ac/len(picks_cat)*100,1) if picks_cat else 0
                cuotas_ac = [float(p.get("cuota",1) or 1) for p in picks_cat if p.get("estado","").lower()=="acierto"]
                roi_est = round((sum(cuotas_ac)/len(cuotas_ac)-1)*ef/100*100-((100-ef)/100)*100,1) if cuotas_ac else -100
                data_edge.append([cat, str(len(picks_cat)), str(ac), f"{ef}%", f"{roi_est:+.1f}%"])

            t_edge = Table(data_edge, colWidths=[4*cm, 2*cm, 2.5*cm, 3*cm, 3*cm], repeatRows=1)
            t_edge.setStyle(TableStyle([
                ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#1A1A2E")),
                ("TEXTCOLOR", (0,0), (-1,0), colors.white),
                ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
                ("FONTSIZE", (0,0), (-1,-1), 9),
                ("ALIGN", (0,0), (-1,-1), "CENTER"),
                ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.HexColor("#F8F9FA"), colors.white]),
                ("GRID", (0,0), (-1,-1), 0.4, colors.HexColor("#DEE2E6")),
                ("TOPPADDING", (0,0), (-1,-1), 4),
                ("BOTTOMPADDING", (0,0), (-1,-1), 4),
            ]))
            story.append(t_edge)

            # Conclusion
            s_edge = styles["Normal"].clone("se")
            s_edge.fontSize = 9
            picks_valor = [p for p in picks_con_edge if p.get("edge_categoria") in ("EXCELENTE","BUENO")]
            picks_sin = [p for p in picks_con_edge if p.get("edge_categoria") == "SIN VALOR"]
            ac_valor = sum(1 for p in picks_valor if p.get("estado","").lower()=="acierto")
            ef_valor = round(ac_valor/len(picks_valor)*100,1) if picks_valor else 0
            story.append(Spacer(1, 0.2*cm))
            story.append(Paragraph(
                f"<b>Conclusion:</b> Picks con valor vs Pinnacle (EXCELENTE+BUENO): "
                f"{len(picks_valor)} picks, {ef_valor}% efectividad. "
                f"Picks sin valor: {len(picks_sin)}. "
                f"{'El modelo identifica bien el valor.' if ef_valor > 65 else 'Revisar criterios de scoring — el edge no predice bien aun.'}",
                s_edge
            ))
            story.append(Spacer(1, 0.3*cm))
        else:
            s_ne = styles["Normal"].clone("ne")
            s_ne.fontSize = 9
            story.append(Paragraph(
                "Sin datos de edge aun — se generan cuando hay cuotas de Pinnacle disponibles via API.",
                s_ne
            ))
            story.append(Spacer(1, 0.3*cm))
    except Exception:
        pass

    story.append(subtitulo("10. Efectividad Real de Anclas (Score 9.0+ Riesgo 1)"))
    todos_picks_rend = leer_json(PICKS_FILE)
    anc_rend = _anclas_efectividad(todos_picks_rend)
    UMBRAL_COB = 87.0
    if anc_rend["efectividad"] is not None:
        ef_anc = anc_rend["efectividad"]
        estado_anc = "RENTABLE para cobertura" if ef_anc >= UMBRAL_COB else "NECESITA AJUSTE"
        color_anc = colors.HexColor("#27500A") if ef_anc >= UMBRAL_COB else colors.HexColor("#A32D2D")
    else:
        ef_anc = None
        estado_anc = "Sin datos suficientes"
        color_anc = colors.HexColor("#633806")

    data_anc = [
        ["Metrica", "Valor"],
        ["Picks ancla analizados (score 9.0+ riesgo 1)", str(anc_rend["total"])],
        ["Aciertos", str(anc_rend["aciertos"])],
        ["Fallos", str(anc_rend["fallos"])],
        ["Efectividad real", f"{ef_anc}%" if ef_anc is not None else "Sin datos"],
        ["Umbral rentabilidad cobertura", f"{UMBRAL_COB}%"],
        ["Estado sistema", estado_anc],
    ]
    t_anc = Table(data_anc, colWidths=[9*cm, 5*cm], repeatRows=1)
    t_anc.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 9),
        ("ALIGN", (0, 0), (-1, -1), "CENTER"),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.HexColor("#F8F9FA"), colors.white]),
        ("GRID", (0, 0), (-1, -1), 0.4, colors.HexColor("#DEE2E6")),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        ("TEXTCOLOR", (1, -1), (1, -1), color_anc),
        ("FONTNAME", (1, -1), (1, -1), "Helvetica-Bold"),
    ]))
    story.append(t_anc)
    story.append(Spacer(1, 0.3*cm))

    # ── BANK ACUMULADO (escenario 2) ─────────────────────────────────
    story.append(subtitulo("10. Bank Acumulado Historico (desde el inicio)"))
    try:
        historial_acum_pdf = _actualizar_bank_acumulado()
        if historial_acum_pdf and len(historial_acum_pdf) >= 2:
            # Tabla resumen acumulado
            bank_acum_final = historial_acum_pdf[-1].get("bank", BANK_INICIAL)
            resultado_acum = round(bank_acum_final - BANK_INICIAL, 2)
            roi_acum = round(resultado_acum / BANK_INICIAL * 100, 2)
            ops_acum = len(historial_acum_pdf) - 1
            aciertos_acum = sum(1 for h in historial_acum_pdf if h.get("estado") == "acierto")
            fallos_acum = sum(1 for h in historial_acum_pdf if h.get("estado") == "fallo")

            data_acum = [
                ["Escenario", "Diario (reinicia S/500)", "Acumulado (desde inicio)"],
                ["Bank inicial", f"S/ {BANK_INICIAL:.2f} (cada dia)", f"S/ {BANK_INICIAL:.2f} (una vez)"],
                ["Operaciones totales", str(ops_acum), str(ops_acum)],
                ["Aciertos", str(aciertos_acum), str(aciertos_acum)],
                ["Fallos", str(fallos_acum), str(fallos_acum)],
                ["Bank final simulado", f"S/ {datos.get('bank_final', BANK_INICIAL):.2f}",
                 f"S/ {bank_acum_final:.2f}"],
                ["Resultado", f"+/-S/ {round(datos.get('bank_final', BANK_INICIAL)-BANK_INICIAL,2):.2f}",
                 f"+S/ {resultado_acum:.2f}" if resultado_acum >= 0 else f"-S/ {abs(resultado_acum):.2f}"],
                ["ROI", f"{datos.get('roi', 0):.2f}%", f"{roi_acum:+.2f}%"],
            ]
            t_acum = Table(data_acum, colWidths=[5*cm, 5*cm, 5*cm], repeatRows=1)
            t_acum.setStyle(TableStyle([
                ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#1A1A2E")),
                ("TEXTCOLOR", (0,0), (-1,0), colors.white),
                ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
                ("FONTSIZE", (0,0), (-1,-1), 9),
                ("ALIGN", (0,0), (-1,-1), "CENTER"),
                ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.HexColor("#F8F9FA"), colors.white]),
                ("GRID", (0,0), (-1,-1), 0.4, colors.HexColor("#DEE2E6")),
                ("TOPPADDING", (0,0), (-1,-1), 4),
                ("BOTTOMPADDING", (0,0), (-1,-1), 4),
                ("BACKGROUND", (2,1), (2,-1), colors.HexColor("#F0FFF4")),
                ("FONTNAME", (0,-1), (-1,-1), "Helvetica-Bold"),
                ("TEXTCOLOR", (2,-1), (2,-1),
                 colors.HexColor("#27500A") if roi_acum >= 0 else colors.HexColor("#A32D2D")),
            ]))
            story.append(t_acum)
            story.append(Spacer(1, 0.3*cm))

            # Grafico bank acumulado
            try:
                img_acum = _grafico_bank_acumulado(historial_acum_pdf)
                if img_acum and _os_bot.path.exists(img_acum):
                    story.append(RLImage(img_acum, width=16*cm, height=5*cm))
                    story.append(Spacer(1, 0.3*cm))
            except Exception:
                pass
    except Exception:
        pass

    # ── TENDENCIA DE EFECTIVIDAD (picks generales) ───────────────────
    story.append(subtitulo("11. Tendencia de Efectividad General"))
    try:
        img_tend = _grafico_tendencia_efectividad(datos["dias"], anio, mes)
        if img_tend:
            story.append(RLImage(img_tend, width=16*cm, height=5.5*cm))
            story.append(Spacer(1, 0.2*cm))
            # Analisis textual de la tendencia
            dias_vals = [d["aciertos"]/(d["aciertos"]+d["fallos"])*100
                        for _, d in datos["dias"] if (d["aciertos"]+d["fallos"]) > 0]
            if len(dias_vals) >= 2:
                slope_est = (dias_vals[-1] - dias_vals[0]) / max(len(dias_vals)-1, 1)
                if slope_est > 2:
                    tend_txt = f"Tendencia POSITIVA (+{slope_est:.1f}%/dia) — la efectividad mejora con el tiempo."
                elif slope_est < -2:
                    tend_txt = f"Tendencia NEGATIVA ({slope_est:.1f}%/dia) — revisar criterios de scoring y mercados."
                else:
                    tend_txt = f"Tendencia ESTABLE ({slope_est:+.1f}%/dia) — sin cambios significativos."
                s_tend = styles["Normal"].clone("tend")
                s_tend.fontSize = 9
                story.append(Paragraph(f"<b>Analisis:</b> {tend_txt}", s_tend))
            story.append(Spacer(1, 0.3*cm))
    except Exception:
        pass

    # ── ANALISIS DE COMBINADAS CON TENDENCIA Y BANK ───────────────────
    story.append(subtitulo("11. Analisis de Combinadas — Tendencia y Bank"))
    try:
        combinadas_mes_rend = leer_json(COMBINADAS_FILE)
        combinadas_mes_rend = [
            c for c in combinadas_mes_rend
            if (c.get("fecha",""))[:7] == f"{anio}-{mes:02d}"
            and not c.get("sin_combinada")
        ]

        if combinadas_mes_rend:
            cerradas_comb = [c for c in combinadas_mes_rend
                            if c.get("estado","").lower() in ("acierto","fallo")]
            aciertos_comb = sum(1 for c in cerradas_comb if c.get("estado","").lower()=="acierto")
            ef_comb = round(aciertos_comb/len(cerradas_comb)*100,1) if cerradas_comb else 0

            # Simulacion bank combinadas
            bank_c = 500.0
            for c in sorted(combinadas_mes_rend, key=lambda x: x.get("fecha","")):
                if c.get("estado","").lower() not in ("acierto","fallo"):
                    continue
                stake_c = round(bank_c * STAKE_COMBINADA, 2)
                cuota_c = float(c.get("cuota_combinada",1.0) or 1.0)
                if c.get("estado","").lower() == "acierto":
                    bank_c = round(bank_c + stake_c*(cuota_c-1), 2)
                else:
                    bank_c = round(bank_c - stake_c, 2)

            resultado_comb = round(bank_c - 500.0, 2)
            roi_comb = round((resultado_comb/500.0)*100, 2)

            data_comb_stats = [
                ["Metrica Combinadas", "Valor"],
                ["Total combinadas del mes", str(len(combinadas_mes_rend))],
                ["Combinadas cerradas", str(len(cerradas_comb))],
                ["Aciertos", str(aciertos_comb)],
                ["Fallos", str(len(cerradas_comb)-aciertos_comb)],
                ["Efectividad combinadas", f"{ef_comb}%"],
                ["Bank inicial (simulacion)", "S/ 500.00"],
                ["Bank final (simulacion)", f"S/ {bank_c:.2f}"],
                ["Resultado", f"+S/ {resultado_comb:.2f}" if resultado_comb>=0 else f"-S/ {abs(resultado_comb):.2f}"],
                ["ROI combinadas", f"{roi_comb:+.2f}%"],
            ]
            t_comb = Table(data_comb_stats, colWidths=[9*cm, 5*cm], repeatRows=1)
            t_comb.setStyle(TableStyle([
                ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#1A1A2E")),
                ("TEXTCOLOR", (0,0), (-1,0), colors.white),
                ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
                ("FONTSIZE", (0,0), (-1,-1), 9),
                ("ALIGN", (0,0), (-1,-1), "CENTER"),
                ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.HexColor("#F8F9FA"), colors.white]),
                ("GRID", (0,0), (-1,-1), 0.4, colors.HexColor("#DEE2E6")),
                ("TOPPADDING", (0,0), (-1,-1), 4),
                ("BOTTOMPADDING", (0,0), (-1,-1), 4),
                ("TEXTCOLOR", (1,-1), (1,-1),
                 colors.HexColor("#27500A") if resultado_comb>=0 else colors.HexColor("#A32D2D")),
                ("FONTNAME", (1,-1), (1,-1), "Helvetica-Bold"),
            ]))
            story.append(t_comb)
            story.append(Spacer(1, 0.3*cm))

            # Grafico bank combinadas
            img_bank_comb = _grafico_bank_combinadas(combinadas_mes_rend)
            if img_bank_comb:
                story.append(RLImage(img_bank_comb, width=16*cm, height=5*cm))
                story.append(Spacer(1, 0.3*cm))

            # Grafico tendencia combinadas
            img_tend_comb = _grafico_tendencia_combinadas(combinadas_mes_rend)
            if img_tend_comb:
                story.append(RLImage(img_tend_comb, width=16*cm, height=5*cm))
                story.append(Spacer(1, 0.3*cm))

            # Analisis textual combinadas
            if len(cerradas_comb) >= 2:
                s_tc = styles["Normal"].clone("tc")
                s_tc.fontSize = 9
                cuota_prom_comb = round(sum(float(c.get("cuota_combinada",1) or 1)
                                           for c in cerradas_comb) / len(cerradas_comb), 2)
                mejor_tipo = {}
                for c in cerradas_comb:
                    st = c.get("subtipo","prematch")
                    if st not in mejor_tipo:
                        mejor_tipo[st] = {"a":0,"t":0}
                    mejor_tipo[st]["t"] += 1
                    if c.get("estado","").lower()=="acierto":
                        mejor_tipo[st]["a"] += 1
                mejor_st = max(mejor_tipo.items(),
                              key=lambda x: x[1]["a"]/x[1]["t"] if x[1]["t"] else 0)[0]
                story.append(Paragraph(
                    f"<b>Resumen combinadas:</b> Cuota promedio {cuota_prom_comb}x | "
                    f"Tipo mas rentable: {mejor_st.upper()} | "
                    f"ROI simulado: {roi_comb:+.2f}% | "
                    f"{'Sistema RENTABLE' if roi_comb>=0 else 'Sistema en PERDIDA — ajustar criterios'}.",
                    s_tc
                ))
                story.append(Spacer(1, 0.3*cm))
        else:
            s_nc = styles["Normal"].clone("nc")
            s_nc.fontSize = 9
            story.append(Paragraph("Sin combinadas registradas este mes.", s_nc))
            story.append(Spacer(1, 0.3*cm))
    except Exception:
        pass

    story.append(subtitulo("12. Feedback y Aprendizaje"))
    ultimos_7 = [(f, d) for f, d in datos["dias"] if (d["aciertos"]+d["fallos"]) > 0][-7:]
    ef_serie = []
    for f, d in ultimos_7:
        c = d["aciertos"] + d["fallos"]
        ef_serie.append(d["aciertos"] / c * 100 if c else 0)
    if len(ef_serie) >= 2:
        tendencia = ef_serie[-1] - ef_serie[0]
        if tendencia > 5:
            tend_txt = "Tendencia POSITIVA — la efectividad esta mejorando."
        elif tendencia < -5:
            tend_txt = "Tendencia NEGATIVA — la efectividad esta bajando. Revisar criterios."
        else:
            tend_txt = "Tendencia ESTABLE — sin cambios significativos en los ultimos dias."
    else:
        tend_txt = "Insuficientes datos para calcular tendencia."
    if datos["mercados"]:
        mejor_m_glob = max(datos["mercados"].items(), key=lambda x: x[1]["efectividad"])
        peor_m_glob = min(datos["mercados"].items(), key=lambda x: x[1]["efectividad"])
        obs_mercado = (f"Mejor mercado: {mejor_m_glob[0]} ({mejor_m_glob[1]['efectividad']}%). "
                       f"Mercado a revisar: {peor_m_glob[0]} ({peor_m_glob[1]['efectividad']}%).")
    else:
        obs_mercado = "Sin datos de mercado."
    if datos["scores"]:
        mejor_sc = max(datos["scores"].items(), key=lambda x: x[1]["efectividad"])
        obs_score = f"Score mas rentable: {mejor_sc[0]} con {mejor_sc[1]['efectividad']}% de efectividad."
    else:
        obs_score = "Sin datos de score."

    feedback_txt = (
        f"<b>Tendencia:</b> {tend_txt}<br/>"
        f"<b>Mercados:</b> {obs_mercado}<br/>"
        f"<b>Scores:</b> {obs_score}<br/>"
        f"<b>ROI acumulado:</b> {roi_txt} — Bank simulado: S/ {datos['bank_final']:.2f}"
    )
    s = styles["Normal"].clone("fb")
    s.fontSize = 9
    s.leading = 14
    story.append(Paragraph(feedback_txt, s))

    # ── COMBINADA DEL DIA ─────────────────────────────────────────────
    # Combinadas en rendimiento
    try:
        _seccion_combinadas_historico(
            story,
            f"{datos['anio']}-{datos['mes']:02d}-01",
            f"{datos['anio']}-{datos['mes']:02d}-31",
            styles
        )
    except Exception:
        pass
    story.append(Spacer(1, 0.3*cm))

    # Graficos del mes
    try:
        picks_rend_all = leer_json(PICKS_FILE)
        picks_mes_rend = [p for p in picks_rend_all
                          if (p.get("fecha_partido") or p.get("fecha") or "")[:7]
                          == f"{datos['anio']}-{datos['mes']:02d}"]
        if picks_mes_rend:
            tmps_rend = _insertar_graficos_pdf(story, picks_mes_rend, prefijo="rend", styles=styles)
            # PUNTO 2 FIX: NO borrar los PNG aqui. ReportLab los lee recien
            # en doc.build(). Se acumulan en _tmps_pendientes y se borran
            # despues del build.
            _tmps_pendientes.extend(tmps_rend)
    except Exception:
        pass

    # Prematch vs Live en rendimiento
    try:
        picks_rend_all = leer_json(PICKS_FILE)
        picks_mes_rend = [p for p in picks_rend_all
                          if (p.get("fecha_partido") or p.get("fecha") or "")[:7]
                          == f"{datos['anio']}-{datos['mes']:02d}"]
        if picks_mes_rend:
            _seccion_prematch_live_pdf(story, picks_mes_rend, styles, None)
    except Exception:
        pass

    story.append(subtitulo("13. Combinada del Dia"))
    try:
        comb = _armar_combinada_del_dia()
    except Exception:
        comb = None
    if comb and not comb.get("sin_combinada") and comb.get("picks"):
        data_comb = [["#", "Partido", "Jugada", "Score", "Riesgo", "Cuota"]]
        for i, p in enumerate(comb["picks"], 1):
            cuota_p = float(p.get("cuota", 0) or p.get("cuota_minima", 0) or 0)
            data_comb.append([
                str(i),
                p.get("partido", ""),
                p.get("jugada", ""),
                str(p.get("score", "")),
                str(p.get("riesgo", "")),
                str(cuota_p),
            ])
        story.append(tabla(data_comb, col_widths=[0.8*cm, 5*cm, 4*cm, 1.5*cm, 1.5*cm, 2.2*cm]))
        story.append(Spacer(1, 0.2*cm))
        bank_act = datos.get("bank_final", BANK_INICIAL)
        stake_c = round(bank_act * STAKE_COMBINADA, 2)
        ganancia_c = round(stake_c * (comb["cuota_combinada"] - 1), 2)
        resumen_comb = (
            f"<b>Cuota combinada:</b> {comb['cuota_combinada']}  |  "
            f"<b>Stake sugerido (10%):</b> S/ {stake_c:.2f}  |  "
            f"<b>Ganancia potencial:</b> S/ {ganancia_c:.2f}"
        )
        sc = styles["Normal"].clone("sc")
        sc.fontSize = 9
        story.append(Paragraph(resumen_comb, sc))
    else:
        story.append(Paragraph(
            "No hay combinada para hoy: ninguna combinacion alcanza "
            "valor esperado positivo con los criterios actuales "
            "(cada eslabon requiere prob 80%+, cuota 1.50+, sin BTTS).",
            styles["Normal"]
        ))

    doc.build(story)

    # PUNTO 2 FIX: borrar TODOS los temporales DESPUES del build,
    # cuando ReportLab ya leyo las imagenes.
    for tmp in [img_bank, img_ef] + _tmps_pendientes:
        try:
            if tmp and os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass

    return pdf_path


def _guardar_snapshot_rendimiento(datos):
    """Guarda snapshot mensual en feedback.json para aprendizaje futuro."""
    anio, mes = datos["anio"], datos["mes"]
    snapshot = {
        "tipo": "snapshot_rendimiento",
        "fecha_generado": fecha_hora_peru(),
        "periodo": f"{anio}-{mes:02d}",
        "efectividad_global": datos["efectividad"],
        "roi": datos["roi"],
        "bank_final": datos["bank_final"],
        "picks_total": datos["total"],
        "aciertos": datos["aciertos"],
        "fallos": datos["fallos"],
        "mejor_mercado": max(datos["mercados"].items(),
                             key=lambda x: x[1]["efectividad"])[0] if datos["mercados"] else None,
        "peor_mercado": min(datos["mercados"].items(),
                            key=lambda x: x[1]["efectividad"])[0] if datos["mercados"] else None,
        "mejor_liga": next(iter(datos["ligas"]), None),
        "mejor_score_rango": max(datos["scores"].items(),
                                 key=lambda x: x[1]["efectividad"])[0] if datos["scores"] else None,
        "efectividad_hoy": datos["hoy"]["efectividad"],
    }
    reporte_path = _os_bot.path.join(BOT_DIR, f"reporte_{anio}_{mes:02d}.json")
    try:
        reporte_hist = leer_json(reporte_path) if os.path.exists(reporte_path) else []
        if not isinstance(reporte_hist, list):
            reporte_hist = [reporte_hist]
        reporte_hist.append(snapshot)
        guardar_json_lista(reporte_path, reporte_hist)
    except Exception:
        pass
    agregar_json(FEEDBACK_FILE, snapshot)
    return snapshot


async def rendimiento(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /rendimiento — Reporte mensual completo."""
    hoy = fecha_peru_obj()
    anio, mes = hoy.year, hoy.month

    await update.message.reply_text(
        f"Generando reporte de rendimiento para {hoy.strftime('%B %Y')}...\n"
        "Esto puede tomar unos segundos."
    )

    try:
        datos = _calcular_rendimiento_mes(anio, mes)
        if not datos:
            await update.message.reply_text(
                "No encontre picks registrados para este mes todavia."
            )
            return

        # Actualizar resultados picks Y combinadas antes de generar reporte
        actualizar_resultados_automaticos()
        _actualizar_resultado_combinada()

        # Actualizar bank acumulado historico
        historial_acum = _actualizar_bank_acumulado()

        snapshot = _guardar_snapshot_rendimiento(datos)

        # Calcular efectividad anclas para mensaje Telegram
        _todos = leer_json(PICKS_FILE)
        _anc = _anclas_efectividad(_todos)
        if _anc["efectividad"] is not None:
            _ef = _anc["efectividad"]
            anc_msg = f"{_anc['total']} picks | {_anc['aciertos']} aciertos | {_ef}% {'✅' if _ef >= 87 else '⚠️'}"
        else:
            anc_msg = "Sin datos suficientes aun"

        pdf_path = generar_pdf_rendimiento(datos)

        with open(pdf_path, "rb") as f:
            await update.message.reply_document(
                document=f,
                filename=f"Rendimiento_{anio}_{mes:02d}.pdf",
                caption="Reporte completo de rendimiento mensual"
            )

        roi_txt = f"+{datos['roi']}%" if datos["roi"] >= 0 else f"{datos['roi']}%"
        lucro = round(datos["bank_final"] - BANK_INICIAL, 2)
        lucro_emoji = "UP" if lucro >= 0 else "DOWN"
        lucro_txt = f"+S/ {lucro:.2f}" if lucro >= 0 else f"-S/ {abs(lucro):.2f}"
        mejor_m = max(datos["mercados"].items(),
                      key=lambda x: x[1]["efectividad"])[0] if datos["mercados"] else "--"
        mejor_l = next(iter(datos["ligas"]), "--")
        h = datos["hoy"]
        ef_hoy = f"{h['efectividad']}%" if h["efectividad"] is not None else "Sin cerrados"

        # Calcular tendencia general
        dias_vals = [d["aciertos"]/(d["aciertos"]+d["fallos"])*100
                    for _, d in datos["dias"] if (d["aciertos"]+d["fallos"]) > 0]
        if len(dias_vals) >= 2:
            slope_tend = (dias_vals[-1] - dias_vals[0]) / max(len(dias_vals)-1, 1)
            if slope_tend > 2:
                tend_emoji = "\U0001f4c8"
                tend_str = f"Mejorando (+{slope_tend:.1f}%/dia)"
            elif slope_tend < -2:
                tend_emoji = "\U0001f4c9"
                tend_str = f"Bajando ({slope_tend:.1f}%/dia)"
            else:
                tend_emoji = "\u27a1"
                tend_str = "Estable"
        else:
            tend_emoji = "\u2754"
            tend_str = "Sin datos suficientes"

        # Tendencia combinadas
        try:
            combs_tend = leer_json(COMBINADAS_FILE)
            combs_mes = [c for c in combs_tend
                        if (c.get("fecha",""))[:7] == f"{anio}-{mes:02d}"
                        and c.get("estado","").lower() in ("acierto","fallo")
                        and not c.get("sin_combinada")]
            if combs_mes:
                ac_comb = sum(1 for c in combs_mes if c.get("estado","").lower()=="acierto")
                ef_comb_str = f"{round(ac_comb/len(combs_mes)*100,1)}% ({len(combs_mes)} cerradas)"
            else:
                ef_comb_str = "Sin combinadas cerradas"
        except Exception:
            ef_comb_str = "N/D"

        resumen_msg = (
            f"\U0001f4ca *Rendimiento {hoy.strftime('%B %Y')}* — al {hoy.strftime('%d/%m')}\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4cc Picks totales: {datos['total']} | Cerrados: {datos['cerrados']}\n"
            f"\u2705 Aciertos: {datos['aciertos']}  \u274c Fallos: {datos['fallos']}\n"
            f"\U0001f3af Efectividad: *{datos['efectividad']}%*\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4b0 Bank inicial: S/ {BANK_INICIAL:.0f}\n"
            f"\U0001f4b3 Bank actual: S/ {datos['bank_final']:.2f}\n"
            f"Resultado: {lucro_txt} ({roi_txt} ROI)\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f3c6 Mejor mercado: {mejor_m} ({datos['mercados'].get(mejor_m, {}).get('efectividad', 0)}%)\n"
            f"\U0001f30d Mejor liga: {mejor_l} ({datos['ligas'].get(mejor_l, {}).get('efectividad', 0)}%)\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4c5 *Hoy ({h['fecha']}):*\n"
            f"  Picks: {h['total']} | Cerrados: {h['cerrados']}\n"
            f"  \u2705 {h['aciertos']}  \u274c {h['fallos']}  \U0001f3af {ef_hoy}\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f9e0 Snapshot guardado para aprendizaje futuro.\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f3af *Anclas (9.0+ riesgo 1):* {anc_msg}\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"{tend_emoji} *Tendencia general:* {tend_str}\n"
            f"\U0001f3af *Efectividad combinadas:* {ef_comb_str}\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"\U0001f4b0 *Bank acumulado (desde inicio)*\n"
            + (
                f"Bank actual: *S/ {historial_acum[-1]['bank']:.2f}* | "
                f"ROI acum: *{round((historial_acum[-1]['bank']-BANK_INICIAL)/BANK_INICIAL*100,2):+.2f}%*"
                if historial_acum and len(historial_acum) >= 2
                else "Sin historial acumulado aun"
            )
        )

        await update.message.reply_text(resumen_msg, parse_mode="Markdown")

        # La combinada del dia se ve en /resumen_combinadas (no se duplica aqui)

        try:
            os.remove(pdf_path)
        except Exception:
            pass

    except Exception as e:
        await update.message.reply_text(f"Error generando reporte: {e}")


# ─────────────────────────────────────────────
# === Corte centralizado de analisis live (Punto 3) ===
MINUTO_CORTE_LIVE = 80


def _live_minuto_valido(minuto):
    """
    Regla centralizada: a partir del minuto 80 NO se analizan partidos live.
    Devuelve True si el partido AUN puede analizarse (<= 80), False si debe
    descartarse. Aplica a todos los mercados sin excepcion.
    """
    try:
        m = int(minuto)
    except (ValueError, TypeError):
        # Minuto desconocido ("?", None): por seguridad, descartar
        return False
    return m <= MINUTO_CORTE_LIVE


#  /live_all — Analiza todos los partidos en vivo automaticamente
# ─────────────────────────────────────────────

async def live_all(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Analiza todos los partidos en vivo en este momento.
    Notifica cada pick con score >= 7.5 como mensaje individual.
    Guarda los picks en picks_guardados.json para reportes.
    Al final envia resumen con todos los picks encontrados.
    """
    await update.message.reply_text(
        "🔴 *Analizando TODOS los partidos en vivo...*\n"
        "Filtro: score 7.5+ | Notificacion por pick en tiempo real",
        parse_mode="Markdown"
    )

    fixtures = api_get("/fixtures?live=all", use_cache=False)

    if not fixtures:
        await update.message.reply_text(
            "❌ No hay partidos en vivo en este momento."
        )
        return

    await update.message.reply_text(
        f"⚽ {len(fixtures)} partidos en vivo encontrados. Pre-cargando en paralelo..."
    )

    # Pre-cargar estadisticas en paralelo
    try:
        import aiohttp
        async with aiohttp.ClientSession() as _sess_l:
            live_ids = [str(m["fixture"]["id"]) for m in fixtures]
            for i in range(0, len(live_ids), 10):
                lote = live_ids[i:i+10]
                tasks_l = [
                    api_get_async(_sess_l, f"/fixtures/statistics?fixture={fid}", use_cache=False)
                    for fid in lote
                ]
                res_l = await asyncio.gather(*tasks_l, return_exceptions=True)
                for fid, stats in zip(lote, res_l):
                    if not isinstance(stats, Exception) and stats:
                        CACHE[f"/fixtures/statistics?fixture={fid}"] = (time.time(), stats)
                await asyncio.sleep(0.3)
    except Exception:
        pass

    picks_encontrados = []
    analizados = 0
    errores = 0

    for m in fixtures:
        fixture_id = str(m["fixture"]["id"])
        home = m["teams"]["home"]["name"]
        away = m["teams"]["away"]["name"]
        league = m["league"]["name"]
        country = m["league"].get("country", "")
        hora = hora_peru(m["fixture"]["date"])
        minuto = m["fixture"]["status"].get("elapsed", "?")
        marcador_h = m["goals"]["home"] or 0
        marcador_a = m["goals"]["away"] or 0

        # PUNTO 3: corte en minuto 80 - descartar partido sin analizarlo
        if not _live_minuto_valido(minuto):
            continue

        try:
            analisis = analizar_live_fixture(fixture_id)
            analizados += 1

            if not analisis or not analisis.get("sugerencias"):
                continue

            score_live = analisis.get("score_live", 0)

            # Tomar la mejor sugerencia
            mejor = analisis["sugerencias"][0]

            # Criterio V14: el live se filtra por la probabilidad de la
            # sugerencia (>= 70%). El sistema de scoring live es propio y
            # NO se recalibra con las tablas prematch; por eso aqui se usa
            # la probabilidad live directa, no recalibrar_probabilidad.
            prob_live = float(mejor.get("prob", 0) or 0)
            if prob_live < 70:
                continue

            # PUNTO 5: refrescar la cuota con la cuota REAL EN VIVO.
            # analizar_live_fixture trae una cuota estimada/estatica;
            # /odds/live da la cuota actual segun el minuto del partido.
            try:
                cuota_live, book_live = buscar_cuota_live(fixture_id, mejor.get("jugada", ""))
                if cuota_live and cuota_live > 1.0:
                    mejor["cuota"] = cuota_live
                    mejor["cuota_api"] = cuota_live
                    mejor["bookmaker"] = book_live
            except Exception:
                pass

            # Guardar pick live
            guardar_pick_live_automatico(
                fixture_id=fixture_id,
                home=home,
                away=away,
                country=country,
                league=league,
                hora=hora,
                sugerencia=mejor,
                minuto=minuto
            )

            picks_encontrados.append({
                "fixture_id": fixture_id,
                "partido": f"{home} vs {away}",
                "league": league,
                "country": country,
                "minuto": minuto,
                "marcador": f"{marcador_h}-{marcador_a}",
                "score": score_live,
                "jugada": mejor.get("jugada", ""),
                "mercado": mejor.get("mercado", ""),
                "prob": mejor.get("prob", ""),
                "riesgo": mejor.get("riesgo", ""),
                "cuota": mejor.get("cuota", ""),
            })

            # Registrar aprendizaje con minuto para analisis futuro
            agregar_json(APRENDIZAJE_FILE, {
                "tipo": "pick_live_all",
                "fecha": fecha_hoy_peru(),
                "fixture_id": fixture_id,
                "partido": f"{home} vs {away}",
                "league": league,
                "country": country,
                "minuto": minuto,
                "marcador": f"{marcador_h}-{marcador_a}",
                "mercado": mejor.get("mercado", ""),
                "jugada": mejor.get("jugada", ""),
                "score": score_live,
                "riesgo": mejor.get("riesgo", ""),
                "cuota": _cuota_segura(mejor),
                "timestamp": fecha_hora_peru(),
            })

            # Notificacion individual por pick
            if score_live >= 9.0:
                emoji = "\U0001f31f"
                nivel = "ELITE"
            elif score_live >= 8.5:
                emoji = "\u2b50"
                nivel = "TOP"
            else:
                emoji = "\u2705"
                nivel = "7.5+"

            msg = (
                f"{emoji} *{home} vs {away}* [{nivel}]\n"
                f"🏆 {league} | Min: {minuto}' | {marcador_h}-{marcador_a}\n"
                f"🎯 {mejor.get('jugada','')}\n"
                f"Score: {score_live}/10 | Riesgo: {mejor.get('riesgo','')} | "
                f"Prob: {mejor.get('prob','')}% | Cuota: {mejor.get('cuota','')}"
            )
            await update.message.reply_text(msg, parse_mode="Markdown")

        except Exception as e:
            errores += 1
            continue

    # Resumen final
    if not picks_encontrados:
        await update.message.reply_text(
            f"📊 Analisis live completo.\n"
            f"Partidos analizados: {analizados} | Errores: {errores}\n"
            f"No se encontraron picks con score 7.5+ en vivo ahora."
        )
        return

    elite_live = [p for p in picks_encontrados if float(p.get("score",0) or 0) >= 9.0]
    top_live   = [p for p in picks_encontrados if 8.5 <= float(p.get("score",0) or 0) < 9.0]

    picks_encontrados.sort(key=lambda x: float(x.get("score",0) or 0), reverse=True)

    lineas = [
        f"📊 *Resumen /live_all*",
        f"━━━━━━━━━━",
        f"Partidos analizados: {analizados} | Errores: {errores}",
        f"🌟 Elite live (9.0+): {len(elite_live)} picks",
        f"⭐ TOP live (8.5-8.9): {len(top_live)} picks",
        f"Total guardados: {len(picks_encontrados)}",
        f"━━━━━━━━━━",
        f"",
        f"*Top picks:*",
    ]
    for i, pk in enumerate(picks_encontrados[:5], 1):
        lineas.append(
            f"{i}. {pk['partido']} (min {pk['minuto']}') "
            f"— {pk.get('jugada','')} "
            f"| Score: {pk.get('score','')} | {pk.get('marcador','')}"
        )

    await update.message.reply_text(
        "\n".join(lineas),
        parse_mode="Markdown"
    )


# ─────────────────────────────────────────────
#  /analizar_all — Analiza todas las ligas automaticamente
# ─────────────────────────────────────────────

async def analizar_all(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Analiza todos los partidos de hoy en todas las ligas configuradas.
    Guarda picks con score >= 7.5 y reporta en tiempo real + resumen final.
    """
    hoy = fecha_hoy_peru()
    await update.message.reply_text(
        f"🔍 *Analizando TODAS las ligas — {hoy}*\nLigas: {len(EUROPA_LEAGUES)+len(SUDAMERICA_LEAGUES)+len(OTRAS_LEAGUES)} | Filtro: score 7.5+\nEsto puede tardar varios minutos...",
        parse_mode="Markdown"
    )

    ligas_todas = {}
    ligas_todas.update(EUROPA_LEAGUES)
    ligas_todas.update(SUDAMERICA_LEAGUES)
    ligas_todas.update(OTRAS_LEAGUES)

    partidos = obtener_fixtures_por_fecha(ligas_todas, hoy)

    if not partidos:
        await update.message.reply_text("No se encontraron partidos para hoy en ninguna liga.")
        return

    await update.message.reply_text(
        f"\U0001f4cb {len(partidos)} partidos encontrados. Analizando en paralelo..."
    )

    picks_encontrados = []
    errores = 0
    analizados = 0

    # Instalar aiohttp si no esta disponible
    try:
        import aiohttp as _aiohttp_check
    except ImportError:
        import subprocess, sys
        subprocess.run([sys.executable, "-m", "pip", "install", "aiohttp", "--break-system-packages", "-q"])
        import aiohttp as _aiohttp_check

    # Pre-cargar odds en paralelo para acelerar el analisis
    try:
        import aiohttp as _aiohttp_pre
        fixture_ids_pre = [str(p["id"]) for p in partidos]

        async def _do_prefetch(fids):
            async with _aiohttp_pre.ClientSession() as _sess_pre:
                tasks = []
                for fid in fids:
                    tasks.append(api_get_async(_sess_pre, f"/odds?fixture={fid}", use_cache=True, ttl=600))
                await asyncio.gather(*tasks, return_exceptions=True)

        for i in range(0, len(fixture_ids_pre), 10):
            lote = fixture_ids_pre[i:i+10]
            await _do_prefetch(lote)
            await asyncio.sleep(0.3)
    except Exception:
        pass

    for p in partidos:
        try:
            fixture_id = str(p["id"])
            home = p["home"]
            away = p["away"]
            league = p.get("league","")
            country = p.get("country","")
            hora = p.get("hour","")

            # Detectar si es partido de selecciones nacionales
            es_seleccion = _es_partido_selecciones(league, country)

            if es_seleccion:
                # Analisis especifico para selecciones
                round_name = p.get("round","")
                analisis_sel = analizar_seleccion(
                    fixture_id, home, away, league, country, hora, round_name
                )
                analizados += 1

                if not analisis_sel or not analisis_sel.get("sugerencias"):
                    continue

                top = analisis_sel["sugerencias"][0]
                score = float(analisis_sel.get("score", 0) or 0)

                if score < 8.0:  # umbral mas conservador para selecciones
                    continue

                pick_data = {
                    "fixture_id": fixture_id,
                    "partido": f"{home} vs {away}",
                    "league": league,
                    "country": country,
                    "hora": hora,
                    "fecha_partido": hoy,
                    "tipo": "prematch",
                    "es_seleccion": True,
                    "fase_torneo": analisis_sel.get("fase",""),
                    "rank_home": analisis_sel.get("rank_home"),
                    "rank_away": analisis_sel.get("rank_away"),
                    **top,
                }
                guardar_pick_plano(pick_data)
                picks_encontrados.append(pick_data)

                emoji = "\U0001f30d"
                cuota_pick = _cuota_segura(top)
                alertas_str = ""
                if analisis_sel.get("alertas"):
                    alertas_str = "\n\u26a0\ufe0f " + " | ".join(analisis_sel["alertas"])

                extra = (
                    f"\U0001f3c6 {analisis_sel.get('fase','')} | "
                    f"FIFA: #{analisis_sel.get('rank_home','?')} vs #{analisis_sel.get('rank_away','?')}\n"
                    f"H2H: {analisis_sel.get('h2h_home_wins',0)}W-"
                    f"{analisis_sel.get('h2h_empates',0)}D-"
                    f"{analisis_sel.get('h2h_away_wins',0)}L | "
                    f"Prom goles: {analisis_sel.get('goles_h2h_prom','?')}\n"
                    f"Estilo: {analisis_sel.get('estilo_home','?')} vs {analisis_sel.get('estilo_away','?')} | "
                    f"Descanso: {analisis_sel.get('desc_home','?')}d vs {analisis_sel.get('desc_away','?')}d\n"
                    f"Bajas: {analisis_sel.get('bajas_home',0)} local | {analisis_sel.get('bajas_away',0)} visitante\n"
                )
                motivo_top = top.get("motivo","")
                await update.message.reply_text(
                    f"{emoji} *{home} vs {away}* [SELECCION]\n"
                    f"\U0001f310 {country} | \U0001f3c6 {league} | \U0001f552 {hora}\n"
                    + extra +
                    f"\U0001f3af {top.get('jugada','')}\n"
                    f"Score: {score}/10 | Riesgo: {top.get('riesgo','')} | "
                    f"Prob: {top.get('prob','')}% | Cuota: {cuota_pick if cuota_pick else 'N/D'}\n"
                    f"\U0001f4a1 {motivo_top}"
                    + alertas_str,
                    parse_mode="Markdown"
                )

            else:
                # Analisis normal de clubes
                # PUNTO 2: incluir_odds=True para usar cuota Pinnacle real,
                # igual que /top. Mismo motor de decision para ambos.
                data = preparar_analisis(
                    fixture_id,
                    incluir_odds=True,
                    incluir_contexto=False
                )
                analizados += 1

                if not data or not data.get("recomendaciones"):
                    continue

                top = data["recomendaciones"][0]
                score = float(top.get("score", 0) or 0)

                # El pick ya paso por preparar_analisis: recalibracion +
                # filtro de cuota 1.50 ya aplicados. Aqui solo se exige una
                # probabilidad recalibrada minima para guardar (mismo
                # criterio que el resto del sistema). NO se filtra por score
                # crudo: tras recalibrar, el score 7.5+ descartaria casi
                # todo y los picks no entrarian al resumen.
                prob_rec = float(top.get("prob", 0) or 0)
                if prob_rec < 70:
                    continue

                # Usar cuota real de la API si existe, si no la calculada
                cuota_real_api = top.get("cuota_api") or top.get("cuota_minima") or 0
                try:
                    cuota_real_api = float(cuota_real_api) if cuota_real_api else 0
                except Exception:
                    cuota_real_api = 0

                pick_data = {
                    "fixture_id": fixture_id,
                    "partido": f"{home} vs {away}",
                    "league": league,
                    "country": country,
                    "hora": hora,
                    "fecha_partido": hoy,
                    "tipo": "prematch",
                    "cuota": cuota_real_api if cuota_real_api > 1.0 else _cuota_segura(top),
                    **top,
                }
                guardar_pick_plano(pick_data)
                picks_encontrados.append(pick_data)

                if score >= 9.0:
                    emoji = "\U0001f31f"
                elif score >= 8.5:
                    emoji = "\u2b50"
                else:
                    emoji = "\u2705"

                cuota_pick = cuota_real_api if cuota_real_api > 1.0 else _cuota_segura(top)
                book_str = f" ({top.get('bookmaker','')})" if top.get("bookmaker") else ""

                # Calcular edge vs Pinnacle
                edge_val = edge_estimado(float(top.get("prob",0) or 0), cuota_pick) if cuota_pick > 1.0 else None
                cat_edge, label_edge = clasificar_edge(edge_val)
                edge_str = ""
                if edge_val is not None:
                    if cat_edge in ("EXCELENTE","BUENO"):
                        edge_str = f"\n\U0001f4b9 *Valor vs Pinnacle: {label_edge}* [{cat_edge}]"
                    elif cat_edge == "LEVE":
                        edge_str = f"\n\U0001f4b9 Valor vs Pinnacle: {label_edge}"
                    elif cat_edge == "SIN VALOR":
                        edge_str = f"\n\u26a0\ufe0f Sin valor vs Pinnacle ({label_edge})"
                await update.message.reply_text(
                    f"{emoji} *{home} vs {away}*\n"
                    f"\U0001f310 {country} | \U0001f3c6 {league} | \U0001f552 {hora}\n"
                    f"\U0001f3af {top.get('jugada','')}\n"
                    f"Score: {score}/10 | Riesgo: {top.get('riesgo','')} | "
                    f"Prob: {top.get('prob','')}% | Cuota: {cuota_pick if cuota_pick else 'N/D'}{book_str}"
                    + edge_str,
                    parse_mode="Markdown"
                )

        except Exception as e:
            errores += 1
            continue

    # Resumen final
    if not picks_encontrados:
        await update.message.reply_text(
            f"📊 Analisis completo.\nPartidos analizados: {analizados}\n"
            f"No se encontraron picks que superen los criterios de hoy "
            f"(prob recalibrada 70%+, cuota 1.50+)."
        )
        return

    # Clasificacion por PROBABILIDAD recalibrada (coherente con el filtro
    # de guardado). Elite = prob >= 85%, resto = los demas guardados.
    elite = [p for p in picks_encontrados
             if float(p.get("prob", 0) or 0) >= 85]
    top75 = [p for p in picks_encontrados
             if float(p.get("prob", 0) or 0) < 85]

    # Intentar armar combinada del dia
    comb = _armar_combinada_del_dia()
    if comb and not comb.get("sin_combinada"):
        _guardar_combinada(comb)

    lineas_res = [
        f"📊 *Resumen /analizar_all — {hoy}*",
        "━━━━━━━━━━",
        f"Partidos analizados: {analizados} | Errores: {errores}",
        f"🌟 Elite (prob 85%+): {len(elite)} picks",
        f"⭐ Resto guardados: {len(top75)} picks",
        f"Total guardados: {len(picks_encontrados)}",
        "━━━━━━━━━━",
    ]
    if comb and not comb.get("sin_combinada"):
        lineas_res.append(f"🎯 Combinada optima: {comb['cuota_combinada']}x ({comb['n_picks']} picks)")
    elif comb and comb.get("sin_combinada"):
        lineas_res.append(f"🚫 {comb.get('motivo','Sin combinada rentable')}")

    # Top 3 picks del dia
    picks_encontrados.sort(key=lambda x: float(x.get("score",0) or 0), reverse=True)
    lineas_res.append("")
    lineas_res.append("*Top 3 picks del dia:*")
    for i, pk in enumerate(picks_encontrados[:3], 1):
        lineas_res.append(f"{i}. {pk['partido']} — {pk.get('jugada','')} (Score: {pk.get('score','')})")
    resumen = "\n".join(lineas_res)

    await update.message.reply_text(resumen, parse_mode="Markdown")


# ─────────────────────────────────────────────
#  PREMATCH vs LIVE — Comparativa para reportes
# ─────────────────────────────────────────────

def _comparativa_prematch_live(picks):
    """
    Analiza picks y devuelve comparativa prematch vs live:
    efectividad, mercados, tendencias por tipo.
    """
    prematch = [p for p in picks if p.get("tipo", "prematch") == "prematch"
                and p.get("estado", "").lower() in ("acierto", "fallo")]
    live     = [p for p in picks if p.get("tipo", "") == "live"
                and p.get("estado", "").lower() in ("acierto", "fallo")]

    def stats_tipo(grupo):
        if not grupo:
            return {"total": 0, "aciertos": 0, "fallos": 0, "efectividad": None, "mercados": {}}
        ac = sum(1 for p in grupo if p.get("estado","").lower() == "acierto")
        fa = len(grupo) - ac
        ef = round(ac / len(grupo) * 100, 1) if grupo else None
        # Por mercado
        mercados = {}
        for p in grupo:
            jugada = p.get("jugada", "Otro")
            if "Corner" in jugada: m = "Corners"
            elif "goles" in jugada.lower(): m = "Goles"
            elif "Tarjeta" in jugada: m = "Tarjetas"
            elif "BTTS" in jugada or "Ambos" in jugada: m = "BTTS"
            elif "1X" in jugada or "X2" in jugada: m = "Doble Oport."
            else: m = "Otro"
            if m not in mercados:
                mercados[m] = {"total": 0, "aciertos": 0}
            mercados[m]["total"] += 1
            if p.get("estado","").lower() == "acierto":
                mercados[m]["aciertos"] += 1
        # Efectividad por mercado
        for m in mercados:
            t = mercados[m]["total"]
            a = mercados[m]["aciertos"]
            mercados[m]["efectividad"] = round(a/t*100,1) if t else 0
        return {"total": len(grupo), "aciertos": ac, "fallos": fa,
                "efectividad": ef, "mercados": mercados}

    stats_pre = stats_tipo(prematch)
    stats_liv = stats_tipo(live)

    # Ganador por tipo
    ef_pre = stats_pre["efectividad"] or 0
    ef_liv = stats_liv["efectividad"] or 0
    if ef_pre > ef_liv:
        ganador = "PREMATCH"
    elif ef_liv > ef_pre:
        ganador = "LIVE"
    else:
        ganador = "EMPATE"

    # Mejor mercado global
    todos_mercados = {}
    for p in picks:
        if p.get("estado","").lower() not in ("acierto","fallo"): continue
        jugada = p.get("jugada","Otro")
        if "Corner" in jugada: m = "Corners"
        elif "goles" in jugada.lower(): m = "Goles"
        elif "Tarjeta" in jugada: m = "Tarjetas"
        elif "BTTS" in jugada or "Ambos" in jugada: m = "BTTS"
        elif "1X" in jugada or "X2" in jugada: m = "Doble Oport."
        else: m = "Otro"
        if m not in todos_mercados:
            todos_mercados[m] = {"total":0,"aciertos":0}
        todos_mercados[m]["total"] += 1
        if p.get("estado","").lower() == "acierto":
            todos_mercados[m]["aciertos"] += 1

    mejor_mercado = None
    mejor_ef = 0
    for m, v in todos_mercados.items():
        if v["total"] >= 3:
            ef = round(v["aciertos"]/v["total"]*100,1)
            if ef > mejor_ef:
                mejor_ef = ef
                mejor_mercado = m

    return {
        "prematch": stats_pre,
        "live": stats_liv,
        "ganador": ganador,
        "mejor_mercado_global": mejor_mercado,
        "mejor_mercado_ef": mejor_ef,
    }


def _seccion_prematch_live_pdf(story, picks, styles, cm_unit):
    """Agrega seccion comparativa prematch vs live al PDF."""
    from reportlab.lib.units import cm as _cm
    comp = _comparativa_prematch_live(picks)

    def subtit(txt):
        s = styles["Heading2"].clone("slh")
        s.fontSize = 11
        s.textColor = colors.HexColor("#16213E")
        s.spaceBefore = 10
        s.spaceAfter = 4
        return Paragraph(txt, s)

    story.append(subtit("Comparativa: Prematch vs Live"))

    pre = comp["prematch"]
    liv = comp["live"]

    def ef_txt(v):
        return f"{v}%" if v is not None else "Sin datos"

    data_comp = [
        ["Metrica", "Prematch", "Live", "Ganador"],
        ["Total cerrados", str(pre["total"]), str(liv["total"]), "—"],
        ["Aciertos", str(pre["aciertos"]), str(liv["aciertos"]), "—"],
        ["Fallos", str(pre["fallos"]), str(liv["fallos"]), "—"],
        ["Efectividad", ef_txt(pre["efectividad"]), ef_txt(liv["efectividad"]),
         comp["ganador"]],
    ]

    # Mercados por tipo
    todos_m = set(list(pre["mercados"].keys()) + list(liv["mercados"].keys()))
    for m in sorted(todos_m):
        pre_m = pre["mercados"].get(m, {})
        liv_m = liv["mercados"].get(m, {})
        pre_ef = f"{pre_m.get('efectividad',0)}% ({pre_m.get('total',0)} picks)" if pre_m else "—"
        liv_ef = f"{liv_m.get('efectividad',0)}% ({liv_m.get('total',0)} picks)" if liv_m else "—"
        ganador_m = ""
        if pre_m and liv_m:
            ganador_m = "PRE" if pre_m.get("efectividad",0) >= liv_m.get("efectividad",0) else "LIVE"
        data_comp.append([m, pre_ef, liv_ef, ganador_m])

    t_comp = Table(data_comp, colWidths=[4*_cm, 4*_cm, 4*_cm, 3*_cm], repeatRows=1)
    t_comp.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#1A1A2E")),
        ("TEXTCOLOR", (0,0), (-1,0), colors.white),
        ("FONTNAME", (0,0), (-1,0), "Helvetica-Bold"),
        ("FONTSIZE", (0,0), (-1,-1), 9),
        ("ALIGN", (0,0), (-1,-1), "CENTER"),
        ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.HexColor("#F8F9FA"), colors.white]),
        ("GRID", (0,0), (-1,-1), 0.4, colors.HexColor("#DEE2E6")),
        ("TOPPADDING", (0,0), (-1,-1), 4),
        ("BOTTOMPADDING", (0,0), (-1,-1), 4),
    ]))
    story.append(t_comp)
    story.append(Spacer(1, 0.2*_cm))

    if comp["mejor_mercado_global"]:
        s = styles["Normal"].clone("pv")
        s.fontSize = 9
        story.append(Paragraph(
            f"Mejor mercado global: <b>{comp['mejor_mercado_global']}</b> "
            f"con {comp['mejor_mercado_ef']}% de efectividad. "
            f"Tipo mas rentable: <b>{comp['ganador']}</b>.",
            s
        ))
    story.append(Spacer(1, 0.3*_cm))



# ─────────────────────────────────────────────
#  COMBINADA LIVE y COMBINADA MIXTA
# ─────────────────────────────────────────────

def _obtener_picks_live_ahora(score_min=7.5, riesgo_max=2):
    """
    Analiza todos los partidos en vivo ahora mismo y devuelve
    picks que cumplan los criterios de calidad.
    Cada pick incluye el minuto actual del partido.
    """
    fixtures = api_get("/fixtures?live=all", use_cache=False)
    if not fixtures:
        return []

    picks_live = []
    for m in fixtures:
        fixture_id = str(m["fixture"]["id"])
        home = m["teams"]["home"]["name"]
        away = m["teams"]["away"]["name"]
        league = m["league"]["name"]
        country = m["league"].get("country", "")
        hora = hora_peru(m["fixture"]["date"])
        minuto = m["fixture"]["status"].get("elapsed", 0) or 0
        gh = m["goals"]["home"] or 0
        ga = m["goals"]["away"] or 0

        try:
            analisis = analizar_live_fixture(fixture_id)
            if not analisis or not analisis.get("sugerencias"):
                continue

            score_live = float(analisis.get("score_live", 0) or 0)
            if score_live < score_min:
                continue

            # Descartar picks de partidos en minuto > 80
            if minuto > 80:
                continue

            mejor = analisis["sugerencias"][0]
            # Verificar riesgo con excepcion para tarjetas
            if not _riesgo_ok(mejor, riesgo_max=riesgo_max):
                continue

            cuota = _cuota_segura(mejor)
            if cuota < CUOTA_MINIMA_PICK:
                continue

            # Excluir BTTS de combinadas live
            if _es_btts(mejor):
                continue

            # ── Verificar que la jugada aun tenga valor (no realizada ya) ──
            jugada_check = mejor.get("jugada", "")
            mercado_check = mejor.get("mercado", "")
            jugada_invalida = False

            # Obtener stats actuales del partido
            stats_check = api_get(f"/fixtures/statistics?fixture={fixture_id}", use_cache=False)
            corners_actuales = 0
            tarjetas_actuales = 0
            if stats_check:
                for td in stats_check:
                    for item in td.get("statistics", []):
                        tipo_s = item.get("type", "")
                        try:
                            val_s = int(str(item.get("value") or 0).replace("%","").strip() or 0)
                        except Exception:
                            val_s = 0
                        if tipo_s == "Corner Kicks":
                            corners_actuales += val_s
                        elif tipo_s == "Yellow Cards":
                            tarjetas_actuales += val_s
                        elif tipo_s == "Red Cards":
                            tarjetas_actuales += val_s * 2

            # Corners: si ya se superó la linea, la jugada ya ocurrió (sin valor)
            if "Corners Over" in jugada_check:
                import re as _re
                m_linea = _re.search(r"(\d+\.?\d*)", jugada_check.split("Over")[-1])
                if m_linea:
                    linea_c = float(m_linea.group(1))
                    if corners_actuales > linea_c:
                        jugada_invalida = True  # Ya se cumplió
                    # Si faltan pocos minutos y quedan pocos corners por llegar
                    minutos_restantes = max(90 - minuto, 0)
                    corners_necesarios = linea_c - corners_actuales
                    if corners_necesarios <= 0:
                        jugada_invalida = True  # Ya cumplida
                    elif minutos_restantes < 5 and corners_necesarios > 3:
                        jugada_invalida = True  # Imposible en tiempo restante

            # Tarjetas: mismo criterio
            elif "Tarjetas Over" in jugada_check:
                import re as _re2
                m_linea2 = _re2.search(r"(\d+\.?\d*)", jugada_check.split("Over")[-1])
                if m_linea2:
                    linea_t = float(m_linea2.group(1))
                    if tarjetas_actuales > linea_t:
                        jugada_invalida = True  # Ya se cumplió
                    minutos_restantes_t = max(90 - minuto, 0)
                    tarjetas_necesarias = linea_t - tarjetas_actuales
                    if tarjetas_necesarias <= 0:
                        jugada_invalida = True
                    elif minutos_restantes_t < 5 and tarjetas_necesarias > 2:
                        jugada_invalida = True

            # Goles: verificar que la linea aun sea alcanzable
            elif "Over" in jugada_check and "gol" in jugada_check.lower():
                import re as _re3
                m_linea3 = _re3.search(r"(\d+\.?\d*)", jugada_check.split("Over")[-1])
                if m_linea3:
                    linea_g = float(m_linea3.group(1))
                    total_goles = gh + ga
                    if total_goles > linea_g:
                        jugada_invalida = True  # Ya cumplida
            elif "Under" in jugada_check and "gol" in jugada_check.lower():
                import re as _re4
                m_linea4 = _re4.search(r"(\d+\.?\d*)", jugada_check.split("Under")[-1])
                if m_linea4:
                    linea_u = float(m_linea4.group(1))
                    total_goles_u = gh + ga
                    if total_goles_u >= linea_u:
                        jugada_invalida = True  # Ya no es posible

            if jugada_invalida:
                continue  # Descartar pick sin valor

            picks_live.append({
                "fixture_id": fixture_id,
                "partido": f"{home} vs {away}",
                "league": league,
                "country": country,
                "hora": hora,
                "minuto_consulta": minuto,
                "marcador": f"{gh}-{ga}",
                "score": score_live,
                "riesgo": riesgo,
                "probabilidad": mejor.get("prob", 0),
                "cuota": cuota if cuota > 1.0 else 0.0,
                "cuota_minima": cuota if cuota > 1.0 else 0.0,
                "mercado": mejor.get("mercado", ""),
                "jugada": mejor.get("jugada", ""),
                "tipo": "live",
                "fecha": fecha_hoy_peru(),
                "fecha_partido": fecha_hoy_peru(),
            })
        except Exception:
            continue

    return picks_live


def _armar_combinada_live():
    """
    Arma la mejor combinada con picks live del momento.
    Criterios: score >= 7.5, riesgo <= 2, cuota >= 1.20.
    El bot decide 2 o 3 picks segun la formula de valor.
    Cuota minima combinada: 2.50x.
    Guarda aprendizaje automaticamente.
    """
    from itertools import combinations as _comb

    hoy = fecha_hoy_peru()
    candidatos = _obtener_picks_live_ahora(score_min=7.5, riesgo_max=2)

    if not candidatos:
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_combinada_live",
            "subtipo": "live",
            "fecha": hoy,
            "motivo": "No hay partidos live con score 8.5+ riesgo 2 ahora mismo",
            "candidatos": 0,
            "timestamp": fecha_hora_peru(),
        })
        return {
            "sin_combinada": True,
            "subtipo": "live",
            "fecha": hoy,
            "motivo": f"No hay picks live con score 8.5+ y riesgo 2 en este momento",
        }

    mejor = None
    mejor_valor = 0.0   # solo combinadas con VE > 0
    mejor_razon = ""

    for n in [3, 2]:
        if len(candidatos) < n:
            continue
        for grupo in _comb(candidatos, n):
            grupo = list(grupo)
            # Verificar que sean partidos distintos
            ids = [p["fixture_id"] for p in grupo]
            if len(set(ids)) < len(ids):
                continue
            cuota_comb = 1.0
            for p in grupo:
                cuota_comb *= float(p.get("cuota", 1.0) or 1.0)
            cuota_comb = round(cuota_comb, 2)
            if cuota_comb < CUOTA_COMBINADA_MIN:
                continue
            if cuota_comb > CUOTA_COMBINADA_MAX:
                continue
            valor = _valor_combinada(grupo)
            if valor > mejor_valor:
                mejor_valor = valor
                mejor = grupo
                mejor_razon = (
                    f"{'Triple' if n==3 else 'Doble'} live optima — "
                    f"cuota {cuota_comb}x | VE={valor}"
                )

    if not mejor:
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_combinada_live",
            "subtipo": "live",
            "fecha": hoy,
            "motivo": f"Ninguna combinacion live supera 2.50x ({len(candidatos)} candidatos)",
            "candidatos": len(candidatos),
            "timestamp": fecha_hora_peru(),
        })
        return {
            "sin_combinada": True,
            "subtipo": "live",
            "fecha": hoy,
            "motivo": f"Ninguna combinacion live supera 2.50x ({len(candidatos)} candidatos disponibles)",
        }

    cuota_combinada = round(sum([1]) * 1.0, 2)
    cuota_combinada = 1.0
    for p in mejor:
        cuota_combinada *= float(p.get("cuota", 1.0) or 1.0)
    cuota_combinada = round(cuota_combinada, 2)

    scores  = [float(p.get("score", 0) or 0) for p in mejor]
    riesgos = [float(p.get("riesgo", 0) or 0) for p in mejor]
    minutos = [int(p.get("minuto_consulta", 0) or 0) for p in mejor]

    resultado = {
        "fecha": hoy,
        "subtipo": "live",
        "picks": mejor,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "razon_seleccion": mejor_razon,
        "score_promedio": round(sum(scores)/len(scores), 2),
        "riesgo_promedio": round(sum(riesgos)/len(riesgos), 2),
        "minuto_promedio": round(sum(minutos)/len(minutos), 0),
        "estado": "pendiente",
        "timestamp": fecha_hora_peru(),
    }

    agregar_json(APRENDIZAJE_FILE, {
        "tipo": "combinada_generada",
        "subtipo": "live",
        "fecha": hoy,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "score_promedio": resultado["score_promedio"],
        "riesgo_promedio": resultado["riesgo_promedio"],
        "minuto_promedio": resultado["minuto_promedio"],
        "partidos": [p["partido"] for p in mejor],
        "timestamp": fecha_hora_peru(),
    })

    return resultado


def _armar_combinada_mixta():
    """
    Arma la mejor combinada mezclando picks prematch del dia
    y picks live del momento.
    El bot decide cuantos de cada tipo para maximizar valor.
    Cuota minima combinada: 2.50x.
    Guarda aprendizaje automaticamente.
    """
    from itertools import combinations as _comb

    hoy = fecha_hoy_peru()

    # Candidatos prematch: todos los pendientes de hoy sin filtros
    picks_todos = leer_json(PICKS_FILE)
    candidatos_pre = []
    for p in picks_todos:
        fecha_pick = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if fecha_pick != hoy:
            continue
        if p.get("tipo", "") != "prematch":
            continue
        if p.get("estado", "pendiente").lower() not in ("pendiente", "pendiente_manual"):
            continue
        cuota = _cuota_segura(p)
        if cuota <= 0:
            continue
        # Verificar que el partido aun no haya comenzado
        hora_pick = p.get("hora", p.get("hour", ""))
        if hora_pick:
            try:
                hora_actual = fecha_peru_obj().strftime("%H:%M")
                if hora_pick <= hora_actual:
                    continue  # Partido ya empezó
            except Exception:
                pass
        p2 = dict(p)
        p2["_fuente"] = "prematch"
        candidatos_pre.append(p2)

    # Candidatos live: todos los del momento con score 7.5+
    candidatos_live = _obtener_picks_live_ahora(score_min=7.5, riesgo_max=3)
    for p in candidatos_live:
        p["_fuente"] = "live"

    todos = candidatos_pre + candidatos_live

    if len(todos) < 2 or not candidatos_pre or not candidatos_live:
        motivo = (
            f"Se necesita al menos 1 prematch pendiente y 1 live. "
            f"Disponibles: {len(candidatos_pre)} prematch + {len(candidatos_live)} live"
        )
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_combinada_mixta",
            "subtipo": "mixta",
            "fecha": hoy,
            "motivo": motivo,
            "candidatos_pre": len(candidatos_pre),
            "candidatos_live": len(candidatos_live),
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": "mixta", "fecha": hoy, "motivo": motivo}

    mejor = None
    mejor_valor = 0.0   # solo combinadas con VE > 0
    mejor_razon = ""

    for n in [3, 2]:
        if len(todos) < n:
            continue
        for grupo in _comb(todos, n):
            grupo = list(grupo)
            # Debe tener al menos 1 prematch y 1 live
            fuentes = [p.get("_fuente", "prematch") for p in grupo]
            if "prematch" not in fuentes or "live" not in fuentes:
                continue
            # Partidos distintos
            ids = [p.get("fixture_id", "") for p in grupo]
            if len(set(ids)) < len(ids):
                continue
            cuota_comb = 1.0
            for p in grupo:
                cuota_comb *= max(_cuota_segura(p), 1.0)
            cuota_comb = round(cuota_comb, 2)
            if cuota_comb < CUOTA_COMBINADA_MIN:
                continue
            if cuota_comb > CUOTA_COMBINADA_MAX:
                continue
            valor = _valor_combinada(grupo)
            if valor > mejor_valor:
                mejor_valor = valor
                mejor = grupo
                n_pre = fuentes.count("prematch")
                n_liv = fuentes.count("live")
                mejor_razon = (
                    f"Mixta {n_pre} prematch + {n_liv} live — "
                    f"cuota {cuota_comb}x | VE={valor}"
                )

    if not mejor:
        motivo = f"Ninguna combinacion mixta supera 2.50x ({len(candidatos_pre)} pre + {len(candidatos_live)} live)"
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_combinada_mixta",
            "subtipo": "mixta",
            "fecha": hoy,
            "motivo": motivo,
            "candidatos_pre": len(candidatos_pre),
            "candidatos_live": len(candidatos_live),
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": "mixta", "fecha": hoy, "motivo": motivo}

    cuota_combinada = 1.0
    for p in mejor:
        cuota_combinada *= float(p.get("cuota", 0) or p.get("cuota_minima", 0) or 1.0)
    cuota_combinada = round(cuota_combinada, 2)

    scores  = [float(p.get("score", 0) or 0) for p in mejor]
    riesgos = [float(p.get("riesgo", 0) or 0) for p in mejor]
    fuentes = [p.get("_fuente", "prematch") for p in mejor]

    resultado = {
        "fecha": hoy,
        "subtipo": "mixta",
        "picks": mejor,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "n_prematch": fuentes.count("prematch"),
        "n_live": fuentes.count("live"),
        "valor_optimizacion": mejor_valor,
        "razon_seleccion": mejor_razon,
        "score_promedio": round(sum(scores)/len(scores), 2),
        "riesgo_promedio": round(sum(riesgos)/len(riesgos), 2),
        "estado": "pendiente",
        "timestamp": fecha_hora_peru(),
    }

    agregar_json(APRENDIZAJE_FILE, {
        "tipo": "combinada_generada",
        "subtipo": "mixta",
        "fecha": hoy,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "n_prematch": resultado["n_prematch"],
        "n_live": resultado["n_live"],
        "valor_optimizacion": mejor_valor,
        "score_promedio": resultado["score_promedio"],
        "riesgo_promedio": resultado["riesgo_promedio"],
        "partidos": [p["partido"] for p in mejor],
        "timestamp": fecha_hora_peru(),
    })

    return resultado


def _formato_combinada_extendido(combinada, bank_actual=None):
    """
    Formatea combinada live o mixta para Telegram.
    Extiende _formato_combinada_telegram con info de minuto y tipo.
    """
    if not combinada:
        return "No hay combinada disponible."

    if combinada.get("sin_combinada"):
        subtipo = combinada.get("subtipo", "").upper()
        motivo_txt = combinada.get("motivo", "")
        return (
            f"🚫 *Sin combinada {subtipo} disponible*\n"
            + motivo_txt + "\n"
            + "El bot seguira monitoreando."
        )

    bank = bank_actual or BANK_INICIAL
    stake = round(bank * STAKE_COMBINADA, 2)
    cuota_comb = combinada.get("cuota_combinada", 1.0)
    ganancia_pot = round(stake * (cuota_comb - 1), 2)

    subtipo = combinada.get("subtipo", "").upper()
    n = combinada.get("n_picks", len(combinada.get("picks", [])))
    tipo_str = "TRIPLE" if n == 3 else "DOBLE"

    ticket_id_ext = combinada.get("ticket_id", "")
    lineas = [
        f"🎯 *COMBINADA {tipo_str} {subtipo} — {combinada['fecha']}*",
        f"🎟 Ticket: `{ticket_id_ext}`" if ticket_id_ext else "",
        f"📊 Score prom: {combinada.get('score_promedio','?')} | "
        f"Riesgo prom: {combinada.get('riesgo_promedio','?')}",
    ]
    lineas = [l for l in lineas if l]

    if subtipo == "MIXTA":
        lineas.append(
            f"📋 Composicion: {combinada.get('n_prematch',0)} prematch + "
            f"{combinada.get('n_live',0)} live"
        )

    lineas.append("━━━━━━━━━━")

    for i, p in enumerate(combinada.get("picks", []), 1):
        cuota_p = _cuota_segura(p)
        fuente = p.get("_fuente", p.get("tipo", "prematch")).upper()
        minuto = p.get("minuto_consulta", p.get("minuto", ""))
        marcador = p.get("marcador", "")

        if fuente == "LIVE":
            lineas.append(
                f"{i}. [LIVE Min:{minuto}'] *{p.get('partido', '')}* {marcador}\n"
                f"   \U0001f310 {p.get('country','')} | \U0001f3c6 {p.get('league','')}\n"
                f"   \U0001f3af {p.get('jugada', '')}\n"
                f"   Score: {p.get('score', '')} | Riesgo: {p.get('riesgo', '')} | "
                f"Prob: {p.get('probabilidad',p.get('prob',''))}% | Cuota: {cuota_p if cuota_p else 'N/D'}"
            )
        else:
            lineas.append(
                f"{i}. [PREMATCH] *{p.get('partido', '')}*\n"
                f"   \U0001f310 {p.get('country','')} | \U0001f3c6 {p.get('league','')} | \U0001f552 {p.get('hora',p.get('hour',''))}\n"
                f"   \U0001f3af {p.get('jugada', '')}\n"
                f"   Score: {p.get('score', '')} | Riesgo: {p.get('riesgo', '')} | "
                f"Prob: {p.get('probabilidad',p.get('prob',''))}% | Cuota: {cuota_p if cuota_p else 'N/D'}"
            )

    lineas += [
        "━━━━━━━━━━",
        f"📊 Cuota combinada: *{cuota_comb}x*",
        f"💰 Stake sugerido (10% bank): *S/ {stake:.2f}*",
        f"📈 Ganancia potencial: *S/ {ganancia_pot:.2f}*",
        f"🧠 {combinada.get('razon_seleccion', '')}",
    ]
    return "\n".join(lineas)


async def combinada_live(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /combinada_live — combinada optima con picks live del momento."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text(
        "🔴 Analizando partidos en vivo para armar combinada...\nEsto puede tomar unos segundos."
    )

    try:
        comb = _armar_combinada_live()
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada live guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        msg = _formato_combinada_extendido(comb)
        await update.message.reply_text(msg, parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error generando combinada live: {e}")


async def combinada_mixta(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /combinada_mixta — combinada optima mezclando prematch y live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text(
        "🎯 Armando combinada mixta (prematch + live)...\nEvaluando todas las combinaciones posibles."
    )

    try:
        comb = _armar_combinada_mixta()
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada mixta guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        msg = _formato_combinada_extendido(comb)
        await update.message.reply_text(msg, parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error generando combinada mixta: {e}")



# ─────────────────────────────────────────────
#  COMBINADAS CUOTA ALTA (minimo 3.0x)
#  /comb3, /comb3_live, /comb3_mixta
# ─────────────────────────────────────────────

CUOTA_MIN_ALTA = 3.0
# Migrado a criterios V14: cuota minima por eslabon 1.50 (igual que el
# resto del sistema). Estos comandos buscan cuota combinada alta, pero
# cada eslabon debe seguir siendo rentable individualmente.
CUOTA_MIN_PICK_ALTA = 1.50
SCORE_MIN_ALTA = 7.5
RIESGO_MAX_ALTA = 3


def _armar_comb3_prematch():
    """
    Combinada cuota alta prematch: mismos criterios que /combinada
    (todos los picks prematch pendientes del dia, sin filtro de score/cuota por pick).
    La diferencia es que la cuota combinada final debe ser >= 3.0x.
    """
    from itertools import combinations as _comb
    hoy = fecha_hoy_peru()
    picks_todos = leer_json(PICKS_FILE)

    ya_usados_c3p = _fixture_ids_ya_usados(hoy)
    candidatos = []
    for p in picks_todos:
        fecha_pick = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if fecha_pick != hoy:
            continue
        if p.get("tipo", "") != "prematch":
            continue
        if p.get("estado", "pendiente").lower() not in ("pendiente", "pendiente_manual"):
            continue
        cuota = _cuota_segura(p)
        if cuota <= 0:
            continue
        # Excluir BTTS
        if _es_btts(p):
            continue
        # Riesgo maximo 3 (excepcion: tarjetas)
        if not _riesgo_ok(p, riesgo_max=3):
            continue
        fid = str(p.get("fixture_id",""))
        if fid and fid in ya_usados_c3p:
            continue
        hora_pick = p.get("hora", p.get("hour", ""))
        if hora_pick:
            try:
                hora_actual = fecha_peru_obj().strftime("%H:%M")
                if hora_pick <= hora_actual:
                    continue
            except Exception:
                pass
        candidatos.append(p)

    return _evaluar_comb3(candidatos, subtipo="prematch", hoy=hoy)


def _armar_comb3_live():
    """
    Combinada cuota alta live: mismos criterios que /combinada_live
    (todos los picks live del momento con score 7.5+, sin filtro de cuota por pick).
    La diferencia es que la cuota combinada final debe ser >= 3.0x.
    """
    from itertools import combinations as _comb
    hoy = fecha_hoy_peru()
    candidatos = _obtener_picks_live_ahora(score_min=7.5, riesgo_max=10)
    # Solo descartar si no hay cuota en absoluto
    candidatos = [p for p in candidatos if _cuota_segura(p) > 0]

    return _evaluar_comb3(candidatos, subtipo="live", hoy=hoy)


def _armar_comb3_mixta():
    """
    Combinada cuota alta mezclando prematch del dia y live del momento.
    Debe tener al menos 1 de cada tipo.
    """
    hoy = fecha_hoy_peru()
    picks_todos = leer_json(PICKS_FILE)

    ya_usados_mix = _fixture_ids_ya_usados(hoy)
    candidatos_pre = []
    for p in picks_todos:
        fecha_pick = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if fecha_pick != hoy or p.get("tipo", "") != "prematch":
            continue
        if p.get("estado", "pendiente").lower() not in ("pendiente", "pendiente_manual"):
            continue
        cuota = _cuota_segura(p)
        if cuota <= 0:
            continue
        # Excluir BTTS
        if _es_btts(p):
            continue
        # Riesgo maximo 3 (excepcion: tarjetas)
        if not _riesgo_ok(p, riesgo_max=3):
            continue
        # No repetir partidos ya usados en otras combinadas del dia
        fid = str(p.get("fixture_id",""))
        if fid and fid in ya_usados_mix:
            continue
        hora_pick = p.get("hora", p.get("hour", ""))
        if hora_pick:
            try:
                hora_actual = fecha_peru_obj().strftime("%H:%M")
                if hora_pick <= hora_actual:
                    continue
            except Exception:
                pass
        p2 = dict(p)
        p2["_fuente"] = "prematch"
        candidatos_pre.append(p2)

    candidatos_live = _obtener_picks_live_ahora(score_min=7.5, riesgo_max=3)
    candidatos_live = [p for p in candidatos_live if _cuota_segura(p) > 0]
    for p in candidatos_live:
        p["_fuente"] = "live"

    todos = candidatos_pre + candidatos_live

    if len(todos) < 2 or not candidatos_pre or not candidatos_live:
        motivo = (
            f"Se necesita al menos 1 prematch y 1 live. "
            f"Disponibles: {len(candidatos_pre)} prematch + {len(candidatos_live)} live"
        )
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_comb3",
            "subtipo": "mixta_alta",
            "fecha": hoy,
            "motivo": motivo,
            "candidatos_pre": len(candidatos_pre),
            "candidatos_live": len(candidatos_live),
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": "mixta_alta", "fecha": hoy, "motivo": motivo}

    return _evaluar_comb3(todos, subtipo="mixta_alta", hoy=hoy, mixta=True)


def _evaluar_comb3(candidatos, subtipo, hoy, mixta=False):
    """
    Evalua todas las combinaciones de 2 y 3 picks
    con cuota minima 3.0x y elige la de mayor valor.
    """
    from itertools import combinations as _comb

    if not candidatos:
        motivo = f"No hay picks con score {SCORE_MIN_ALTA}+ riesgo {RIESGO_MAX_ALTA} cuota {CUOTA_MIN_PICK_ALTA}+"
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_comb3",
            "subtipo": subtipo,
            "fecha": hoy,
            "motivo": motivo,
            "candidatos": 0,
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": subtipo, "fecha": hoy, "motivo": motivo}

    # Filtro por eslabon (criterios V14): cada pick debe ser valido
    # individualmente. Estos comandos buscan cuota combinada alta, pero
    # un eslabon flojo invalida el ticket igual que en /combinada.
    candidatos = [p for p in candidatos if _eslabon_valido_combinada(p)]
    if not candidatos:
        motivo = ("Ningun pick pasa el filtro por eslabon V14 "
                  f"(prob>={COMB_PROB_MIN}%, score>={COMB_SCORE_MIN}, "
                  f"cuota>={CUOTA_MINIMA_ESLABON}, sin BTTS)")
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_comb3",
            "subtipo": subtipo,
            "fecha": hoy,
            "motivo": motivo,
            "candidatos": 0,
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": subtipo,
                "fecha": hoy, "motivo": motivo}

    mejor = None
    mejor_valor = 0.0   # solo combinadas con VALOR ESPERADO > 0
    mejor_razon = ""

    for n in [3, 2]:
        if len(candidatos) < n:
            continue
        for grupo in _comb(candidatos, n):
            grupo = list(grupo)
            # Partidos distintos
            ids = [p.get("fixture_id", "") for p in grupo]
            if len(set(ids)) < len(ids):
                continue
            # Si es mixta: al menos 1 prematch y 1 live
            if mixta:
                fuentes = [p.get("_fuente", "prematch") for p in grupo]
                if "prematch" not in fuentes or "live" not in fuentes:
                    continue
            cuota_comb = 1.0
            for p in grupo:
                cuota_comb *= max(_cuota_segura(p), 1.0)
            cuota_comb = round(cuota_comb, 2)
            # Cuota combinada minima alta (proposito de estos comandos).
            # No hay tope superior: el filtro de VE descarta lo fragil.
            if cuota_comb < CUOTA_MIN_ALTA:
                continue
            valor = _valor_combinada(grupo)
            if valor > mejor_valor:
                mejor_valor = valor
                mejor = grupo
                fuentes_str = ""
                if mixta:
                    fs = [p.get("_fuente", "pre") for p in grupo]
                    fuentes_str = (f" ({fs.count('prematch')}pre+"
                                   f"{fs.count('live')}live)")
                mejor_razon = (
                    f"{'Triple' if n==3 else 'Doble'}{fuentes_str} "
                    f"cuota alta — {cuota_comb}x | VE={valor}"
                )

    if not mejor:
        motivo = (f"Ninguna combinacion con VE>0 supera {CUOTA_MIN_ALTA}x "
                  f"({len(candidatos)} candidatos validos)")
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": "sin_comb3",
            "subtipo": subtipo,
            "fecha": hoy,
            "motivo": motivo,
            "candidatos": len(candidatos),
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": subtipo, "fecha": hoy, "motivo": motivo}

    cuota_combinada = 1.0
    for p in mejor:
        cuota_combinada *= float(p.get("cuota", 0) or p.get("cuota_minima", 0) or 1.0)
    cuota_combinada = round(cuota_combinada, 2)

    scores  = [float(p.get("score", 0) or 0) for p in mejor]
    riesgos = [float(p.get("riesgo", 0) or 0) for p in mejor]
    fuentes = [p.get("_fuente", "prematch") for p in mejor]

    resultado = {
        "fecha": hoy,
        "subtipo": subtipo,
        "tipo_cuota": "alta_3x",
        "picks": mejor,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "razon_seleccion": mejor_razon,
        "score_promedio": round(sum(scores)/len(scores), 2),
        "riesgo_promedio": round(sum(riesgos)/len(riesgos), 2),
        "estado": "pendiente",
        "timestamp": fecha_hora_peru(),
    }
    if mixta:
        resultado["n_prematch"] = fuentes.count("prematch")
        resultado["n_live"] = fuentes.count("live")

    # Aprendizaje
    aprendizaje_entry = {
        "tipo": "comb3_generada",
        "subtipo": subtipo,
        "fecha": hoy,
        "cuota_combinada": cuota_combinada,
        "cuota_min_pick": CUOTA_MIN_PICK_ALTA,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "score_promedio": resultado["score_promedio"],
        "riesgo_promedio": resultado["riesgo_promedio"],
        "partidos": [p.get("partido","") for p in mejor],
        "jugadas": [p.get("jugada","") for p in mejor],
        "cuotas_individuales": [
            float(p.get("cuota",0) or p.get("cuota_minima",0) or 0)
            for p in mejor
        ],
        "timestamp": fecha_hora_peru(),
    }
    if mixta:
        aprendizaje_entry["n_prematch"] = fuentes.count("prematch")
        aprendizaje_entry["n_live"] = fuentes.count("live")
    agregar_json(APRENDIZAJE_FILE, aprendizaje_entry)

    return resultado


def _formato_comb3_telegram(combinada, bank_actual=None):
    """Formatea combinada cuota alta para Telegram."""
    if not combinada:
        return "No hay combinada disponible."

    if combinada.get("sin_combinada"):
        subtipo = combinada.get("subtipo", "").upper().replace("_ALTA","")
        motivo_c3 = combinada.get("motivo", "")
        return (
            f"🚫 *Sin comb3 {subtipo}*\n"
            + motivo_c3 + "\n"
            + f"Recuerda: picks cuota >= {CUOTA_MIN_PICK_ALTA}, combinada >= {CUOTA_MIN_ALTA}x."
        )

    bank = bank_actual or BANK_INICIAL
    stake = round(bank * STAKE_COMBINADA, 2)  # 10% del bank para combinadas
    cuota_comb = combinada.get("cuota_combinada", 1.0)
    ganancia_pot = round(stake * (cuota_comb - 1), 2)

    subtipo = combinada.get("subtipo", "").upper().replace("_ALTA","")
    n = combinada.get("n_picks", len(combinada.get("picks", [])))
    tipo_str = "TRIPLE" if n == 3 else "DOBLE"

    ticket_id_c3 = combinada.get("ticket_id", "")
    lineas = [
        f"💰 *COMB3 {tipo_str} {subtipo} — {combinada['fecha']}*",
        f"🎟 Ticket: `{ticket_id_c3}`" if ticket_id_c3 else "",
        f"📊 Cuota min. {CUOTA_MIN_ALTA}x | Score prom: {combinada.get('score_promedio','?')} | Riesgo prom: {combinada.get('riesgo_promedio','?')}",
    ]

    if combinada.get("n_prematch") is not None:
        lineas.append(
            f"📋 {combinada.get('n_prematch',0)} prematch + {combinada.get('n_live',0)} live"
        )

    lineas.append("━━━━━━━━━━")

    for i, p in enumerate(combinada.get("picks", []), 1):
        cuota_p = float(p.get("cuota", 0) or p.get("cuota_minima", 0) or 0)
        fuente = p.get("_fuente", p.get("tipo", "prematch")).upper()
        minuto = p.get("minuto_consulta", "")
        extra = f" | Min: {minuto}'" if fuente == "LIVE" and minuto else ""

        lineas.append(
            f"{i}. [{fuente}] *{p.get('partido','')}*{extra}\n"
            f"   {p.get('jugada','')} | Score: {p.get('score','')} | "
            f"Riesgo: {p.get('riesgo','')} | 💰 Cuota: {cuota_p}"
        )

    lineas += [
        "━━━━━━━━━━",
        f"🎯 Cuota combinada: *{cuota_comb}x*",
        f"💰 Stake sugerido (10% bank): *S/ {stake:.2f}*",
        f"📈 Ganancia potencial: *S/ {ganancia_pot:.2f}*",
        f"🧠 {combinada.get('razon_seleccion','')}",
    ]
    return "\n".join(lineas)


async def comb3(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /comb3 — combinada cuota alta (3x+) con picks prematch."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text(
        "💰 Armando combinada cuota alta prematch (min 3.0x)..."
    )
    try:
        comb = _armar_comb3_prematch()
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
        await update.message.reply_text(
            _formato_comb3_telegram(comb), parse_mode="Markdown"
        )
    except Exception as e:
        await update.message.reply_text(f"❌ Error en comb3: {e}")


async def comb3_live(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /comb3_live — combinada cuota alta (3x+) con picks live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text(
        "🔴 Analizando partidos live para combinada cuota alta (min 3.0x)..."
    )
    try:
        comb = _armar_comb3_live()
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
        await update.message.reply_text(
            _formato_comb3_telegram(comb), parse_mode="Markdown"
        )
    except Exception as e:
        await update.message.reply_text(f"❌ Error en comb3_live: {e}")


async def comb3_mixta(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /comb3_mixta — combinada cuota alta (3x+) mixta prematch + live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text(
        "🎯 Armando combinada cuota alta mixta prematch+live (min 3.0x)..."
    )
    try:
        comb = _armar_comb3_mixta()
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
        await update.message.reply_text(
            _formato_comb3_telegram(comb), parse_mode="Markdown"
        )
    except Exception as e:
        await update.message.reply_text(f"❌ Error en comb3_mixta: {e}")

async def reparar_cuotas(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /reparar_cuotas — Recorre picks_guardados.json y agrega el campo
    "cuota" a todos los picks que solo tienen "cuota_minima".
    Necesario para que las combinadas funcionen con picks antiguos.
    """
    picks = leer_json(PICKS_FILE)
    reparados = 0
    for p in picks:
        cuota_actual = p.get("cuota")
        cuota_min = p.get("cuota_minima")
        # Si no tiene cuota o es 0/None, usar cuota_minima
        try:
            cuota_f = float(cuota_actual) if cuota_actual is not None else 0.0
        except (ValueError, TypeError):
            cuota_f = 0.0
        if cuota_f <= 0:
            try:
                cuota_min_f = float(cuota_min) if cuota_min is not None else 0.0
            except (ValueError, TypeError):
                cuota_min_f = 0.0
            if cuota_min_f > 0:
                p["cuota"] = cuota_min_f
                reparados += 1
            # Si cuota_minima tampoco tiene valor, dejar en 0
        # Asegurar fecha_partido existe
        if not p.get("fecha_partido") and p.get("fecha"):
            p["fecha_partido"] = p["fecha"]

    guardar_json_lista(PICKS_FILE, picks)
    await update.message.reply_text(
        f"🔧 *Reparacion completada*\n"
        f"Picks revisados: {len(picks)}\n"
        f"Picks reparados: {reparados}\n"
        f"Ahora las combinadas deberian encontrar mas candidatos.",
        parse_mode="Markdown"
    )



# ─────────────────────────────────────────────
#  RESUMENES DIARIOS ESPECIALIZADOS
#  /resumen_prematch, /resumen_live, /resumen_combinadas
# ─────────────────────────────────────────────

def _generar_pdf_resumen_especializado(picks_filtrados, titulo, filename, hoy):
    """
    Genera un PDF de resumen especializado con los picks filtrados.
    Reutiliza el formato de generar_pdf_resumentop.
    """
    def score_pick(p):
        try:
            return float(p.get("score", 0) or 0)
        except Exception:
            return 0

    picks_ord = sorted(picks_filtrados, key=score_pick, reverse=True)

    total = len(picks_ord)
    ganados = sum(1 for p in picks_ord if p.get("estado","").lower() == "acierto")
    perdidos = sum(1 for p in picks_ord if p.get("estado","").lower() == "fallo")
    pendientes = total - ganados - perdidos
    cerrados = ganados + perdidos
    efectividad = round((ganados / cerrados) * 100, 1) if cerrados > 0 else 0

    c = canvas.Canvas(_tmp_path(filename), pagesize=A4)
    width, height = A4
    y = height - 50

    c.setFont("Helvetica-Bold", 16)
    c.drawString(40, y, titulo)
    y -= 30

    c.setFont("Helvetica-Bold", 11)
    c.drawString(40, y, f"Fecha: {hoy}  |  Generado: {fecha_hora_peru()} Hora Peru")
    y -= 25

    c.setFont("Helvetica", 10)
    stats = [
        f"Total picks: {total}",
        f"Aciertos: {ganados}",
        f"Fallos: {perdidos}",
        f"Pendientes: {pendientes}",
        f"Efectividad: {efectividad}%",
    ]
    for stat in stats:
        c.drawString(40, y, stat)
        y -= 16
    y -= 10

    # Linea separadora
    c.setStrokeColorRGB(0.1, 0.1, 0.1)
    c.line(40, y, width - 40, y)
    y -= 15

    c.setFont("Helvetica", 10)
    for i, p in enumerate(picks_ord, 1):
        cuota_p = p.get("cuota") or p.get("cuota_minima") or "N/D"
        minuto = p.get("minuto_consulta","")
        hora_extra = f" | Min: {minuto}'" if minuto else ""
        lineas = [
            f"{i}. {p.get('partido','N/D')}",
            f"   {p.get('country','N/D')} | {p.get('league', p.get('liga','N/D'))} | {p.get('hora', p.get('hour',''))} Hora Peru{hora_extra}",
            f"   Mercado: {p.get('mercado','N/D')} | Jugada: {p.get('jugada','N/D')}",
            f"   Score: {p.get('score','N/D')} | Riesgo: {p.get('riesgo','N/D')} | Prob: {p.get('probabilidad', p.get('prob','N/D'))}% | Cuota: {cuota_p}",
            f"   Estado: {p.get('estado','pendiente').upper()} | Resultado: {p.get('resultado_real','pendiente')}",
        ]
        for linea in lineas:
            if y < 80:
                c.showPage()
                y = height - 50
                c.setFont("Helvetica", 10)
            c.drawString(40, y, linea[:110])
            y -= 14
        # Linea divisoria entre picks
        c.setStrokeColorRGB(0.8, 0.8, 0.8)
        c.line(40, y, width - 40, y)
        y -= 10

    c.save()
    return _tmp_path(filename)


def _mensaje_resumen_especializado(picks, tipo_label, hoy):
    """Genera el mensaje de Telegram para el resumen especializado."""
    total = len(picks)
    ganados = sum(1 for p in picks if p.get("estado","").lower() == "acierto")
    perdidos = sum(1 for p in picks if p.get("estado","").lower() == "fallo")
    pendientes = total - ganados - perdidos
    cerrados = ganados + perdidos
    ef = round(ganados/cerrados*100, 1) if cerrados > 0 else 0

    lineas = [
        f"\U0001f4cb *{tipo_label} — {hoy}*",
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"Total: {total} | \u2705 {ganados} | \u274c {perdidos} | \u23f3 {pendientes}",
        f"Efectividad: *{ef}%*" if cerrados > 0 else "Sin picks cerrados aun",
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
    ]

    # Top 5 picks por score
    picks_ord = sorted(picks, key=lambda p: float(p.get("score",0) or 0), reverse=True)
    for i, p in enumerate(picks_ord[:5], 1):
        cuota_p = p.get("cuota") or p.get("cuota_minima") or "N/D"
        estado_e = "\u2705" if p.get("estado","").lower()=="acierto" else "\u274c" if p.get("estado","").lower()=="fallo" else "\u23f3"
        minuto = p.get("minuto_consulta","")
        hora_str = f"Min:{minuto}'" if minuto else p.get("hora", p.get("hour",""))
        lineas.append(
            f"{estado_e} *{p.get('partido','')}* | {hora_str}\n"
            f"   {p.get('jugada','')} | Score:{p.get('score','')} | Cuota:{cuota_p}"
        )

    if total > 5:
        lineas.append(f"\n... y {total-5} picks mas en el PDF")

    return "\n".join(lineas)


async def resumen_prematch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /resumen_prematch — resumen diario solo de picks prematch."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f4cb Generando resumen prematch del dia...")

    picks_todos, _ = actualizar_resultados_automaticos()
    hoy = fecha_hoy_peru()

    picks = [
        p for p in picks_todos
        if (p.get("fecha_partido") or p.get("fecha",""))[:10] == hoy
        and p.get("tipo","prematch") in ("prematch","top","elite","top_manana","elite_manana","")
        and p.get("tipo","prematch") not in ("live","toplive","elitelive")
    ]

    if not picks:
        await update.message.reply_text(
            f"No hay picks prematch registrados para hoy ({hoy})."
        )
        return

    # Mensaje
    msg = _mensaje_resumen_especializado(picks, "RESUMEN PREMATCH", hoy)
    await update.message.reply_text(msg, parse_mode="Markdown")

    # PDF
    try:
        pdf = _generar_pdf_resumen_especializado(
            picks, "RESUMEN PREMATCH — HARRYNINE", "resumen_prematch_hoy.pdf", hoy
        )
        with open(pdf, "rb") as f:
            await update.message.reply_document(
                document=f,
                filename=f"Prematch_{hoy}.pdf",
                caption=f"\U0001f4cb Picks prematch del {hoy}"
            )
    except Exception as e:
        await update.message.reply_text(f"\u274c Error generando PDF: {e}")


async def resumen_live(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /resumen_live — resumen diario solo de picks live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f534 Generando resumen live del dia...")

    picks_todos, _ = actualizar_resultados_automaticos()
    hoy = fecha_hoy_peru()

    picks = [
        p for p in picks_todos
        if (p.get("fecha_partido") or p.get("fecha",""))[:10] == hoy
        and p.get("tipo","") in ("live","toplive","elitelive")
    ]

    if not picks:
        await update.message.reply_text(
            f"No hay picks live registrados para hoy ({hoy})."
        )
        return

    msg = _mensaje_resumen_especializado(picks, "RESUMEN LIVE", hoy)
    await update.message.reply_text(msg, parse_mode="Markdown")

    try:
        pdf = _generar_pdf_resumen_especializado(
            picks, "RESUMEN LIVE — HARRYNINE", "resumen_live_hoy.pdf", hoy
        )
        with open(pdf, "rb") as f:
            await update.message.reply_document(
                document=f,
                filename=f"Live_{hoy}.pdf",
                caption=f"\U0001f534 Picks live del {hoy}"
            )
    except Exception as e:
        await update.message.reply_text(f"\u274c Error generando PDF: {e}")


async def resumen_combinadas(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /resumen_combinadas — resumen diario de todas las combinadas."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f3af Generando resumen de combinadas del dia...")

    hoy = fecha_hoy_peru()
    _actualizar_resultado_combinada()
    combinadas = leer_json(COMBINADAS_FILE)

    # Asignar ticket_id a combinadas que no lo tienen
    import uuid as _uuid_rc
    modificadas = False
    for c in combinadas:
        if not c.get("ticket_id") and not c.get("sin_combinada"):
            subtipo = c.get("subtipo","pre")[:3].upper()
            fecha_c = (c.get("fecha") or hoy).replace("-","")[2:]
            uid = str(_uuid_rc.uuid4())[:6].upper()
            c["ticket_id"] = f"COMB-{subtipo}-{fecha_c}-{uid}"
            modificadas = True
    if modificadas:
        guardar_json_lista(COMBINADAS_FILE, combinadas)

    combs_hoy = [c for c in combinadas if c.get("fecha","")[:10] == hoy]

    if not combs_hoy:
        await update.message.reply_text(
            f"No hay combinadas registradas para hoy ({hoy}).\n"
            "Usa /combinada, /combinada_live, /comb3 etc. para generar combinadas."
        )
        return

    # Mensaje resumen — excluir sin_combinada del conteo
    combs_reales = [c for c in combs_hoy if not c.get("sin_combinada") and c.get("picks")]
    total_c = len(combs_reales)
    aciertos_c = sum(1 for c in combs_reales if c.get("estado","").lower()=="acierto")
    fallos_c = sum(1 for c in combs_reales if c.get("estado","").lower()=="fallo")
    pend_c = total_c - aciertos_c - fallos_c
    cerradas_c = aciertos_c + fallos_c
    ef_c = round(aciertos_c/cerradas_c*100,1) if cerradas_c > 0 else 0
    ef_str = f"Efectividad: *{ef_c}%* ({cerradas_c} cerradas)" if cerradas_c > 0 else "Sin combinadas cerradas aun"

    # Simulacion bank del dia (S/500, 10% por combinada, en orden cronologico)
    bank_dia = BANK_INICIAL
    combs_cerradas_ord = sorted(
        [c for c in combs_reales if c.get("estado","").lower() in ("acierto","fallo")],
        key=lambda x: x.get("timestamp", x.get("fecha",""))
    )
    detalle_bank = []
    for c in combs_cerradas_ord:
        stake_d = round(bank_dia * STAKE_COMBINADA, 2)
        cuota_d = float(c.get("cuota_combinada", 1.0) or 1.0)
        ticket_d = c.get("ticket_id","")[-6:] if c.get("ticket_id") else "?"
        subtipo_d = c.get("subtipo","?").upper().replace("_ALTA","")
        if c.get("estado","").lower() == "acierto":
            ganancia_d = round(stake_d * (cuota_d - 1), 2)
            bank_dia = round(bank_dia + ganancia_d, 2)
            detalle_bank.append(f"  \u2705 [{subtipo_d}] {cuota_d}x | +S/{ganancia_d:.2f} → Bank: S/{bank_dia:.2f}")
        else:
            bank_dia = round(bank_dia - stake_d, 2)
            detalle_bank.append(f"  \u274c [{subtipo_d}] {cuota_d}x | -S/{stake_d:.2f} → Bank: S/{bank_dia:.2f}")

    resultado_dia = round(bank_dia - BANK_INICIAL, 2)
    roi_dia = round(resultado_dia / BANK_INICIAL * 100, 2)
    if resultado_dia >= 0:
        bank_str = f"S/ {bank_dia:.2f} (*+S/ {resultado_dia:.2f}*, ROI: +{roi_dia}%)"
    else:
        bank_str = f"S/ {bank_dia:.2f} (*-S/ {abs(resultado_dia):.2f}*, ROI: {roi_dia}%)"

    lineas_msg = [
        f"\U0001f3af *RESUMEN COMBINADAS — {hoy}*",
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"Total: {total_c} | \u2705 {aciertos_c} | \u274c {fallos_c} | \u23f3 {pend_c}",
        ef_str,
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"\U0001f4b0 *Bank del dia* (S/500, stake 10%)",
    ]
    if detalle_bank:
        lineas_msg += detalle_bank
        lineas_msg.append(f"  \U0001f4ca *Resultado: {bank_str}*")
    else:
        lineas_msg.append(f"  Sin combinadas cerradas aun — Bank: S/ {BANK_INICIAL:.2f}")
    lineas_msg.append(f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")

    for i, c in enumerate(combs_reales, 1):
        estado_e = "\u2705" if c.get("estado","").lower()=="acierto" else "\u274c" if c.get("estado","").lower()=="fallo" else "\u23f3"
        subtipo = c.get("subtipo","pre").upper().replace("_ALTA","")
        n = c.get("n_picks", len(c.get("picks",[])))
        tipo_str = "TRIPLE" if n==3 else "DOBLE"
        ticket = c.get("ticket_id","Sin ticket")
        cuota_c = c.get("cuota_combinada","?")

        # Score promedio y prob promedio de los picks
        picks_c = c.get("picks",[])
        scores = [float(p.get("score",0) or 0) for p in picks_c if p.get("score")]
        probs = [float(p.get("probabilidad",0) or p.get("prob",0) or 0) for p in picks_c]
        score_prom = round(sum(scores)/len(scores),1) if scores else "?"
        prob_prom = round(sum(probs)/len(probs),1) if probs else "?"

        # Linea principal: tipo, cuota, ticket, score, prob
        linea = (
            f"{estado_e} *[{subtipo}] {tipo_str}* | Cuota: {cuota_c}x\n"
            f"   \U0001f39f `{ticket}`\n"
            f"   Score prom: {score_prom} | Prob prom: {prob_prom}%"
        )
        if c.get("estado","").lower() == "fallo" and c.get("fallo_en"):
            linea += f"\n   \u274c Fallo en: {c['fallo_en']}"
        lineas_msg.append(linea)

    await update.message.reply_text("\n".join(lineas_msg), parse_mode="Markdown")

    # PDF
    try:
        c_pdf = canvas.Canvas(_tmp_path("resumen_combinadas_hoy.pdf"), pagesize=A4)
        width, height = A4
        y = height - 50

        c_pdf.setFont("Helvetica-Bold", 16)
        c_pdf.drawString(40, y, "RESUMEN COMBINADAS — HARRYNINE")
        y -= 25
        c_pdf.setFont("Helvetica", 10)
        c_pdf.drawString(40, y, f"Fecha: {hoy} | Generado: {fecha_hora_peru()}")
        y -= 20
        c_pdf.drawString(40, y, f"Total: {total_c} | Aciertos: {aciertos_c} | Fallos: {fallos_c} | Pendientes: {pend_c} | Efectividad: {ef_c}%")
        y -= 25

        for i, c in enumerate(combs_hoy, 1):
            if y < 100:
                c_pdf.showPage()
                y = height - 50
                c_pdf.setFont("Helvetica", 10)

            estado_str = c.get("estado","pendiente").upper()
            subtipo = c.get("subtipo","prematch").upper()
            n = c.get("n_picks", len(c.get("picks",[])))
            tipo_str = "TRIPLE" if n==3 else "DOBLE"

            c_pdf.setFont("Helvetica-Bold", 10)
            c_pdf.drawString(40, y, f"{i}. [{subtipo}] {tipo_str} — Cuota: {c.get('cuota_combinada','?')}x | Estado: {estado_str}")
            y -= 14
            c_pdf.setFont("Helvetica", 9)
            c_pdf.drawString(40, y, f"   Ticket: {c.get('ticket_id','')} | Score prom: {c.get('score_promedio','?')} | Riesgo prom: {c.get('riesgo_promedio','?')}")
            y -= 14

            for j, p in enumerate(c.get("picks",[]), 1):
                cuota_p = _cuota_segura(p) or "N/D"
                minuto = p.get("minuto_consulta","")
                hora_str = f"Min:{minuto}'" if minuto else p.get("hora", p.get("hour",""))
                linea = f"   {j}. {p.get('partido','')} | {p.get('country','')} | {p.get('league','')} | {hora_str}"
                c_pdf.drawString(40, y, linea[:100])
                y -= 12
                linea2 = f"      {p.get('jugada','')} | Score:{p.get('score','')} | Riesgo:{p.get('riesgo','')} | Cuota:{cuota_p}"
                c_pdf.drawString(40, y, linea2[:100])
                y -= 12

            if c.get("fallo_en"):
                c_pdf.drawString(40, y, f"   Fallo en: {c.get('fallo_en','')}")
                y -= 12

            c_pdf.setStrokeColorRGB(0.8, 0.8, 0.8)
            c_pdf.line(40, y, width-40, y)
            y -= 12

        c_pdf.save()
        with open(_tmp_path("resumen_combinadas_hoy.pdf"), "rb") as f:
            await update.message.reply_document(
                document=f,
                filename=f"Combinadas_{hoy}.pdf",
                caption=f"\U0001f3af Combinadas del {hoy}"
            )
    except Exception as e:
        await update.message.reply_text(f"\u274c Error generando PDF combinadas: {e}")

async def actualizar_combinadas_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /actualizar_combinadas — Fuerza la actualizacion de resultados
    de todas las combinadas pendientes cruzando con picks_guardados.json.
    """
    await update.message.reply_text(
        "\U0001f504 Actualizando resultados de combinadas..."
    )
    try:
        actualizar_resultados_automaticos()
        _actualizar_resultado_combinada()

        combinadas = leer_json(COMBINADAS_FILE)
        hoy = fecha_hoy_peru()
        pend = sum(1 for c in combinadas if c.get("estado","") == "pendiente")
        aciertos = sum(1 for c in combinadas if c.get("estado","").lower() == "acierto")
        fallos = sum(1 for c in combinadas if c.get("estado","").lower() == "fallo")

        await update.message.reply_text(
            f"\u2705 *Combinadas actualizadas*\n"
            f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
            f"Total combinadas: {len(combinadas)}\n"
            f"\u2705 Aciertos: {aciertos}\n"
            f"\u274c Fallos: {fallos}\n"
            f"\u23f3 Pendientes: {pend}\n"
            f"\n"
            f"Si alguna sigue como pendiente es porque sus picks "
            f"aun no tienen resultado en picks_guardados.json. "
            f"Usa /reparar_cuotas si hay datos faltantes.",
            parse_mode="Markdown"
        )
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")



# ─────────────────────────────────────────────
#  MODO ESCALERA
#  /escalera — Escalera cronologica de picks
# ─────────────────────────────────────────────

ESCALERA_STAKE_INICIAL = 20.0
ESCALERA_SCORE_MIN = 8.5
ESCALERA_CUOTA_MIN = 1.30

_escaleras_activas = {}  # chat_id -> escalera dict


def _armar_escalera():
    """
    Arma escalera cronologica de picks live + prematch.
    Score >= 8.5, cuota >= 1.30.
    Cada escalon empieza despues que termina el anterior.
    """
    hoy = fecha_hoy_peru()
    hora_actual = fecha_peru_obj().strftime("%H:%M")
    candidatos = []

    # ── Picks LIVE ───────────────────────────────────────────────────
    fixtures_live = api_get("/fixtures?live=all", use_cache=False)
    for m in (fixtures_live or []):
        fixture_id = str(m["fixture"]["id"])
        home = m["teams"]["home"]["name"]
        away = m["teams"]["away"]["name"]
        league = m["league"]["name"]
        country = m["league"].get("country","")
        minuto = m["fixture"]["status"].get("elapsed", 0) or 0
        gh = m["goals"]["home"] or 0
        ga = m["goals"]["away"] or 0
        hora_inicio = hora_peru(m["fixture"]["date"])

        if minuto > 80:
            continue

        try:
            analisis = analizar_live_fixture(fixture_id)
            if not analisis or not analisis.get("sugerencias"):
                continue
            score_live = float(analisis.get("score_live", 0) or 0)
            if score_live < ESCALERA_SCORE_MIN:
                continue
            mejor = analisis["sugerencias"][0]
            cuota = _cuota_segura(mejor)
            if cuota < ESCALERA_CUOTA_MIN:
                continue

            from datetime import timedelta as _td2
            mins_rest = max(90 - minuto, 5)
            hora_fin = (fecha_peru_obj() + _td2(minutes=mins_rest)).strftime("%H:%M")

            candidatos.append({
                "fixture_id": fixture_id,
                "partido": f"{home} vs {away}",
                "league": league,
                "country": country,
                "tipo": "live",
                "minuto": minuto,
                "marcador": f"{gh}-{ga}",
                "hora_inicio": hora_actual,
                "hora_fin_estimada": hora_fin,
                "jugada": mejor.get("jugada",""),
                "mercado": mejor.get("mercado",""),
                "score": score_live,
                "riesgo": float(mejor.get("riesgo",0) or 0),
                "probabilidad": mejor.get("prob",0),
                "cuota": cuota,
                "estado": "pendiente",
            })
        except Exception:
            continue

    # ── Picks PREMATCH pendientes ────────────────────────────────────
    picks_todos = leer_json(PICKS_FILE)
    for p in picks_todos:
        fecha_pick = (p.get("fecha_partido") or p.get("fecha",""))[:10]
        if fecha_pick != hoy:
            continue
        if p.get("tipo","prematch") not in ("prematch",""):
            continue
        if p.get("estado","pendiente").lower() not in ("pendiente","pendiente_manual"):
            continue
        hora_pick = p.get("hora", p.get("hour",""))
        if not hora_pick or hora_pick <= hora_actual:
            continue
        score = float(p.get("score",0) or 0)
        if score < ESCALERA_SCORE_MIN:
            continue
        cuota = _cuota_segura(p)
        if cuota < ESCALERA_CUOTA_MIN:
            continue

        try:
            h2, m2 = map(int, hora_pick.split(":"))
            fin_mins = h2*60 + m2 + 120
            hora_fin = f"{(fin_mins//60)%24:02d}:{fin_mins%60:02d}"
        except Exception:
            hora_fin = hora_pick

        candidatos.append({
            "fixture_id": str(p.get("fixture_id","")),
            "partido": p.get("partido",""),
            "league": p.get("league", p.get("liga","")),
            "country": p.get("country",""),
            "tipo": "prematch",
            "hora_inicio": hora_pick,
            "hora_fin_estimada": hora_fin,
            "jugada": p.get("jugada",""),
            "mercado": p.get("mercado",""),
            "score": float(p.get("score",0) or 0),
            "riesgo": float(p.get("riesgo",0) or 0),
            "probabilidad": p.get("probabilidad", p.get("prob",0)),
            "cuota": cuota,
            "estado": "pendiente",
        })

    if not candidatos:
        return []

    # ── Construir secuencia cronologica ─────────────────────────────
    # Live primero (por score), luego prematch por hora
    live_cands = sorted([c for c in candidatos if c["tipo"]=="live"],
                        key=lambda x: x["score"], reverse=True)
    pre_cands  = sorted([c for c in candidatos if c["tipo"]=="prematch"],
                        key=lambda x: x["hora_inicio"])

    todos = live_cands + pre_cands
    escalera = []
    hora_libre = "00:00"

    for c in todos:
        if c["hora_inicio"] >= hora_libre:
            escalera.append(c)
            hora_libre = c["hora_fin_estimada"]
        if len(escalera) >= 5:
            break

    return escalera


def _formato_escalera(escalera, stake_inicial=ESCALERA_STAKE_INICIAL, idx_actual=None):
    """Formatea la escalera para Telegram."""
    if not escalera:
        return "\u274c No hay picks disponibles para armar escalera ahora."

    acumulado = stake_inicial
    lineas = [
        f"\U0001f4ca *ESCALERA HARRYNINE — {fecha_hoy_peru()}*",
        f"\U0001f4b0 Stake inicial: *S/ {stake_inicial:.2f}* | {len(escalera)} escalones",
        f"\U0001f3af Score min: {ESCALERA_SCORE_MIN}+ | Cuota min: {ESCALERA_CUOTA_MIN}x",
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
    ]

    for i, e in enumerate(escalera):
        cuota = float(e.get("cuota",1.0))
        nuevo_acum = round(acumulado * cuota, 2)
        ganancia = round(nuevo_acum - acumulado, 2)

        if idx_actual is None:
            emoji = "\u23f3"
        elif i < idx_actual:
            emoji = "\u2705"
        elif i == idx_actual:
            emoji = "\U0001f3af"
        else:
            emoji = "\u23f3"

        tipo_str = f"[LIVE Min:{e.get('minuto','')}']" if e["tipo"]=="live" else "[PRE]"
        lineas.append(
            f"{emoji} *Escalon {i+1}* {tipo_str} \u23f0 {e.get('hora_inicio','')}\n"
            f"   {e['partido']} | {e.get('country','')}\n"
            f"   {e['jugada']} | Score:{e['score']} | Cuota:{cuota}x\n"
            f"   Apuesta: S/{acumulado:.2f} \u2192 Si acierta: *S/{nuevo_acum:.2f}* (+S/{ganancia:.2f})"
        )
        acumulado = nuevo_acum

    ganancia_total = round(acumulado - stake_inicial, 2)
    lineas += [
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"\U0001f3c6 Si acierta todo: *S/ {acumulado:.2f}*",
        f"\U0001f4c8 Ganancia neta: *+S/ {ganancia_total:.2f}*",
        f"\u26a0\ufe0f Si falla: pierde S/ {stake_inicial:.2f} iniciales",
    ]
    return "\n".join(lineas)


async def _verificar_escaleras_job(context):
    """Job cada 5 min: verifica escalones activos y notifica resultado."""
    import re as _re_esc

    def _evaluar_pick_esc(jugada, gh, ga, corners, tarjetas):
        jugada_l = jugada.lower()
        total = gh + ga
        def lin(txt):
            m = _re_esc.search(r"(\d+\.?\d*)", txt)
            return float(m.group(1)) if m else None
        if "under" in jugada_l and "gol" in jugada_l:
            l = lin(jugada); return total < l if l else None
        elif "over" in jugada_l and "gol" in jugada_l:
            l = lin(jugada); return total > l if l else None
        elif "ambos marcan" in jugada_l:
            return gh > 0 and ga > 0
        elif "corner" in jugada_l and "over" in jugada_l:
            l = lin(jugada.split("Over")[-1]); return corners > l if l else None
        elif "tarjeta" in jugada_l and "over" in jugada_l:
            l = lin(jugada.split("Over")[-1]); return tarjetas > l if l else None
        elif "1x" in jugada_l: return gh >= ga
        elif "x2" in jugada_l: return ga >= gh
        return None

    for chat_id, esc in list(_escaleras_activas.items()):
        if esc.get("estado") in ("completada","fallida","cancelada"):
            _escaleras_activas.pop(chat_id, None)
            continue

        escalones = esc.get("escalones",[])
        idx = esc.get("escalon_actual", 0)
        if idx >= len(escalones):
            esc["estado"] = "completada"
            continue

        pick = escalones[idx]
        fid = pick.get("fixture_id","")
        if not fid:
            continue

        try:
            fx = api_get(f"/fixtures?id={fid}", use_cache=False)
            if not fx:
                continue
            status = fx[0]["fixture"]["status"]["short"]
            if status not in ("FT","AET","PEN"):
                continue

            gh = fx[0]["goals"]["home"] or 0
            ga = fx[0]["goals"]["away"] or 0
            jugada = pick.get("jugada","")
            corners, tarjetas = 0, 0

            if "corner" in jugada.lower() or "tarjeta" in jugada.lower():
                stats = api_get(f"/fixtures/statistics?fixture={fid}", use_cache=False)
                if stats:
                    for td in stats:
                        for item in td.get("statistics",[]):
                            t = item.get("type","")
                            try: v = int(str(item.get("value") or 0).replace("%","").strip() or 0)
                            except: v = 0
                            if t == "Corner Kicks": corners += v
                            elif t == "Yellow Cards": tarjetas += v
                            elif t == "Red Cards": tarjetas += v * 2

            acierto = _evaluar_pick_esc(jugada, gh, ga, corners, tarjetas)
            if acierto is None:
                continue

            # Calcular bank acumulado hasta este escalon
            bank = esc.get("stake_inicial", ESCALERA_STAKE_INICIAL)
            for j in range(idx):
                bank = round(bank * float(escalones[j].get("cuota",1.0)), 2)

            cuota_act = float(pick.get("cuota",1.0))

            if acierto:
                pick["estado"] = "acierto"
                bank_nuevo = round(bank * cuota_act, 2)
                esc["escalon_actual"] = idx + 1

                if idx + 1 >= len(escalones):
                    esc["estado"] = "completada"
                    ganancia = round(bank_nuevo - esc["stake_inicial"], 2)
                    # Aprendizaje
                    agregar_json(APRENDIZAJE_FILE, {
                        "tipo": "escalera_resultado",
                        "estado": "completada",
                        "fecha": fecha_hoy_peru(),
                        "escalones": len(escalones),
                        "stake_inicial": esc["stake_inicial"],
                        "bank_final": bank_nuevo,
                        "ganancia": ganancia,
                        "roi": round(ganancia/esc["stake_inicial"]*100, 2),
                        "picks": [{"partido":e["partido"],"jugada":e["jugada"],
                                   "score":e["score"],"cuota":e["cuota"],
                                   "tipo":e["tipo"]} for e in escalones],
                        "timestamp": fecha_hora_peru(),
                    })
                    msg = (
                        f"\U0001f3c6 *ESCALERA COMPLETADA!*\n"
                        f"\u2705 Todos los {len(escalones)} escalones acertados\n"
                        f"\U0001f4b0 Bank final: *S/ {bank_nuevo:.2f}*\n"
                        f"\U0001f4c8 Ganancia: *+S/ {ganancia:.2f}* (ROI: +{round(ganancia/esc['stake_inicial']*100,1)}%)\n"
                        f"Usa /escalera para iniciar una nueva."
                    )
                else:
                    prox = escalones[idx + 1]
                    bank_si_prox = round(bank_nuevo * float(prox.get("cuota",1.0)), 2)
                    msg = (
                        f"\u2705 *Escalon {idx+1} ACERTADO!*\n"
                        f"{pick['partido']} | {gh}-{ga}\n"
                        f"\U0001f4b0 Bank: *S/ {bank_nuevo:.2f}*\n"
                        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
                        f"\u23f3 *Escalon {idx+2}:* {prox['partido']}\n"
                        f"\u23f0 {prox.get('hora_inicio','')} | {prox['jugada']} | Cuota:{prox['cuota']}x\n"
                        f"Si acierta: *S/ {bank_si_prox:.2f}*"
                    )
            else:
                pick["estado"] = "fallo"
                esc["estado"] = "fallida"
                perdida = esc["stake_inicial"]
                # Aprendizaje
                agregar_json(APRENDIZAJE_FILE, {
                    "tipo": "escalera_resultado",
                    "estado": "fallida",
                    "fecha": fecha_hoy_peru(),
                    "escalon_fallo": idx + 1,
                    "escalones_completados": idx,
                    "stake_inicial": esc["stake_inicial"],
                    "perdida": perdida,
                    "picks": [{"partido":e["partido"],"jugada":e["jugada"],
                               "score":e["score"],"cuota":e["cuota"],
                               "tipo":e["tipo"]} for e in escalones],
                    "timestamp": fecha_hora_peru(),
                })
                if "corner" in jugada.lower():
                    resultado_str = f"{corners} corners"
                elif "tarjeta" in jugada.lower():
                    resultado_str = f"{tarjetas} tarjetas"
                else:
                    resultado_str = f"{gh}-{ga}"
                msg = (
                    f"\u274c *Escalon {idx+1} FALLIDO*\n"
                    f"{pick['partido']} | {resultado_str}\n"
                    f"\U0001f4b0 Perdida: *S/ {perdida:.2f}*\n"
                    f"La escalera ha terminado. Usa /escalera para intentar de nuevo."
                )

            try:
                await context.bot.send_message(
                    chat_id=chat_id, text=msg, parse_mode="Markdown"
                )
            except Exception:
                pass

        except Exception:
            continue


async def escalera(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /escalera — Arma y muestra escalera cronologica de picks.
    El usuario puede confirmar con /confirmar_escalera o cancelar.
    """
    _registrar_chat_alarma(update.effective_chat.id)
    chat_id = str(update.effective_chat.id)

    # Si ya hay una escalera activa para este chat
    esc_activa = _escaleras_activas.get(chat_id)
    if esc_activa and esc_activa.get("estado") == "activa":
        idx = esc_activa.get("escalon_actual", 0)
        escalones = esc_activa.get("escalones", [])
        msg = _formato_escalera(escalones, esc_activa.get("stake_inicial", ESCALERA_STAKE_INICIAL), idx)
        await update.message.reply_text(
            f"\u26a0\ufe0f Ya tienes una escalera activa (escalon {idx+1}/{len(escalones)}):\n\n"
            + msg + "\n\nUsa /cancelar_escalera para cancelarla.",
            parse_mode="Markdown"
        )
        return

    await update.message.reply_text(
        "\U0001f4ca Armando escalera... analizando picks disponibles."
    )

    escalones = _armar_escalera()

    if not escalones:
        await update.message.reply_text(
            "\u274c No hay suficientes picks con score 8.5+ y cuota 1.30+ "
            "disponibles ahora para armar una escalera.\n"
            "Intenta mas tarde cuando haya mas partidos en curso o proximos."
        )
        return

    # Guardar escalera como propuesta (pendiente de confirmacion)
    _escaleras_activas[chat_id] = {
        "estado": "propuesta",
        "escalones": escalones,
        "stake_inicial": ESCALERA_STAKE_INICIAL,
        "escalon_actual": 0,
        "fecha": fecha_hoy_peru(),
        "timestamp": fecha_hora_peru(),
    }

    msg = _formato_escalera(escalones)
    await update.message.reply_text(msg, parse_mode="Markdown")
    await update.message.reply_text(
        f"\u2753 *Para confirmar* esta escalera escribe /confirmar_escalera\n"
        f"Para cancelar escribe /cancelar_escalera",
        parse_mode="Markdown"
    )


async def confirmar_escalera(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Confirma la escalera propuesta y la activa."""
    chat_id = str(update.effective_chat.id)
    esc = _escaleras_activas.get(chat_id)

    if not esc or esc.get("estado") != "propuesta":
        await update.message.reply_text(
            "No hay escalera pendiente de confirmacion. Usa /escalera para crear una."
        )
        return

    esc["estado"] = "activa"
    escalones = esc["escalones"]
    primer_pick = escalones[0]

    # Activar job de verificacion si no existe
    jobs = context.job_queue.get_jobs_by_name(f"escalera_{chat_id}")
    if not jobs:
        context.job_queue.run_repeating(
            _verificar_escaleras_job,
            interval=300,  # cada 5 minutos
            first=30,
            chat_id=chat_id,
            name=f"escalera_{chat_id}"
        )

    tipo_str = f"LIVE (Min:{primer_pick.get('minuto','')})" if primer_pick["tipo"]=="live" else "PREMATCH"
    await update.message.reply_text(
        f"\u2705 *Escalera activada!*\n"
        f"\U0001f3af {len(escalones)} escalones | Stake: S/ {esc['stake_inicial']:.2f}\n"
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
        f"*Escalon 1 activo:* [{tipo_str}]\n"
        f"{primer_pick['partido']}\n"
        f"{primer_pick['jugada']} | Cuota:{primer_pick['cuota']}x\n"
        f"\n"
        f"El bot te notificara automaticamente cuando termine cada escalon.",
        parse_mode="Markdown"
    )


async def cancelar_escalera(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Cancela la escalera activa o propuesta."""
    chat_id = str(update.effective_chat.id)
    esc = _escaleras_activas.pop(chat_id, None)

    for job in context.job_queue.get_jobs_by_name(f"escalera_{chat_id}"):
        job.schedule_removal()

    if esc:
        await update.message.reply_text(
            f"\u274c Escalera cancelada (estado: {esc.get('estado','?')}).\n"
            "Usa /escalera para crear una nueva."
        )
    else:
        await update.message.reply_text("No habia escalera activa.")


# ─────────────────────────────────────────────
#  COMBINADAS CUOTA 4x y 5x (4 picks minimo)
#  /comb4, /comb4_live, /comb4_mixta
#  /comb5, /comb5_live, /comb5_mixta
# ─────────────────────────────────────────────

CUOTA_MIN_4X = 4.0
CUOTA_MIN_5X = 5.0
# Migrado a criterios V14: cuota minima por eslabon 1.50, igual que todo
# el sistema. El filtro por eslabon (_eslabon_valido_combinada) y el VE>0
# son los que garantizan que la combinada de cuota alta tenga valor real.
CUOTA_MIN_PICK_4X = 1.50
CUOTA_MIN_PICK_5X = 1.50
N_PICKS_ALTA = 4            # Minimo 4 picks para estas combinadas


def _armar_comb_alta(subtipo, cuota_min_comb, cuota_min_pick, hoy, mixta=False):
    """
    Arma combinada de cuota alta (4x o 5x) con 3 o 4 picks.
    subtipo: "prematch", "live", "mixta_4x", "mixta_5x"
    No repite partidos ya usados en otras combinadas del dia.
    """
    from itertools import combinations as _comb_it

    ya_usados = _fixture_ids_ya_usados(hoy)
    hora_actual = fecha_peru_obj().strftime("%H:%M")

    # ── Candidatos prematch ──────────────────────────────────────────
    candidatos_pre = []
    if subtipo in ("prematch", "mixta_4x", "mixta_5x"):
        picks_todos = leer_json(PICKS_FILE)
        for p in picks_todos:
            fecha_pick = (p.get("fecha_partido") or p.get("fecha",""))[:10]
            if fecha_pick != hoy or p.get("tipo","") != "prematch":
                continue
            if p.get("estado","pendiente").lower() not in ("pendiente","pendiente_manual"):
                continue
            cuota = _cuota_segura(p)
            if cuota < cuota_min_pick:
                continue
            # Excluir BTTS
            if _es_btts(p):
                continue
            # Riesgo maximo 3 (excepcion: tarjetas)
            if not _riesgo_ok(p, riesgo_max=3):
                continue
            fid = str(p.get("fixture_id",""))
            if fid and fid in ya_usados:
                continue
            hora_pick = p.get("hora", p.get("hour",""))
            if hora_pick:
                try:
                    if hora_pick <= hora_actual:
                        continue
                except Exception:
                    pass
            p2 = dict(p)
            p2["_fuente"] = "prematch"
            candidatos_pre.append(p2)

    # ── Candidatos live ──────────────────────────────────────────────
    candidatos_live = []
    if subtipo in ("live", "mixta_4x", "mixta_5x"):
        live_raw = _obtener_picks_live_ahora(score_min=7.5, riesgo_max=3)
        for p in live_raw:
            cuota = _cuota_segura(p)
            if cuota < cuota_min_pick:
                continue
            # Tarjetas: excepcion de riesgo ya manejada en _obtener_picks_live_ahora
            fid = str(p.get("fixture_id",""))
            if fid and fid in ya_usados:
                continue
            p["_fuente"] = "live"
            candidatos_live.append(p)

    # Armar pool segun tipo
    if subtipo == "prematch":
        todos = candidatos_pre
    elif subtipo == "live":
        todos = candidatos_live
    else:
        todos = candidatos_pre + candidatos_live

    # Filtro por eslabon (criterios V14): cada pick valido individualmente.
    todos = [p for p in todos if _eslabon_valido_combinada(p)]

    if not todos:
        motivo = (f"Ningun pick pasa el filtro por eslabon V14 "
                  f"(prob>={COMB_PROB_MIN}%, score>={COMB_SCORE_MIN}, "
                  f"cuota>={CUOTA_MINIMA_ESLABON}, sin BTTS)")
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": f"sin_comb_{int(cuota_min_comb)}x",
            "subtipo": subtipo,
            "fecha": hoy,
            "motivo": motivo,
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": subtipo, "fecha": hoy, "motivo": motivo}

    mejor = None
    mejor_valor = 0.0   # solo combinadas con VALOR ESPERADO > 0
    mejor_razon = ""

    # Evaluar combinaciones de 4 y 3 picks
    for n in [4, 3]:
        if len(todos) < n:
            continue
        for grupo in _comb_it(todos, n):
            grupo = list(grupo)
            # Partidos distintos
            ids = [p.get("fixture_id","") for p in grupo]
            if len(set(ids)) < len(ids):
                continue
            # Si mixta: al menos 1 prematch y 1 live
            if mixta or subtipo in ("mixta_4x","mixta_5x"):
                fuentes = [p.get("_fuente","prematch") for p in grupo]
                if "prematch" not in fuentes or "live" not in fuentes:
                    continue
            # Cuota combinada
            cuota_comb = 1.0
            for p in grupo:
                cuota_comb *= max(_cuota_segura(p), 1.0)
            cuota_comb = round(cuota_comb, 2)
            if cuota_comb < cuota_min_comb:
                continue
            valor = _valor_combinada(grupo)
            if valor > mejor_valor:
                mejor_valor = valor
                mejor = grupo
                fs = [p.get("_fuente","pre") for p in grupo]
                mejor_razon = (
                    f"{'Cuadruple' if n==4 else 'Triple'} {subtipo} — "
                    f"{cuota_comb}x | valor={round(valor,4)}"
                )

    if not mejor:
        motivo = f"Ninguna combinacion de 3-4 picks supera {cuota_min_comb}x ({len(todos)} candidatos)"
        agregar_json(APRENDIZAJE_FILE, {
            "tipo": f"sin_comb_{int(cuota_min_comb)}x",
            "subtipo": subtipo,
            "fecha": hoy,
            "motivo": motivo,
            "candidatos": len(todos),
            "timestamp": fecha_hora_peru(),
        })
        return {"sin_combinada": True, "subtipo": subtipo, "fecha": hoy, "motivo": motivo}

    cuota_combinada = 1.0
    for p in mejor:
        cuota_combinada *= max(_cuota_segura(p), 1.0)
    cuota_combinada = round(cuota_combinada, 2)

    scores  = [float(p.get("score",0) or 0) for p in mejor]
    riesgos = [float(p.get("riesgo",0) or 0) for p in mejor]
    fuentes = [p.get("_fuente","prematch") for p in mejor]

    resultado = {
        "fecha": hoy,
        "subtipo": subtipo,
        "tipo_cuota": f"alta_{int(cuota_min_comb)}x",
        "picks": mejor,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "razon_seleccion": mejor_razon,
        "score_promedio": round(sum(scores)/len(scores), 2),
        "riesgo_promedio": round(sum(riesgos)/len(riesgos), 2),
        "estado": "pendiente",
        "timestamp": fecha_hora_peru(),
    }
    if subtipo in ("mixta_4x","mixta_5x"):
        resultado["n_prematch"] = fuentes.count("prematch")
        resultado["n_live"] = fuentes.count("live")

    agregar_json(APRENDIZAJE_FILE, {
        "tipo": f"comb_{int(cuota_min_comb)}x_generada",
        "subtipo": subtipo,
        "fecha": hoy,
        "cuota_combinada": cuota_combinada,
        "n_picks": len(mejor),
        "valor_optimizacion": mejor_valor,
        "score_promedio": resultado["score_promedio"],
        "riesgo_promedio": resultado["riesgo_promedio"],
        "partidos": [p.get("partido","") for p in mejor],
        "cuotas_individuales": [_cuota_segura(p) for p in mejor],
        "timestamp": fecha_hora_peru(),
    })
    return resultado


def _formato_comb_alta(combinada, cuota_objetivo, bank_actual=None):
    """Formatea combinada 4x o 5x para Telegram."""
    if not combinada:
        return "No hay combinada disponible."
    if combinada.get("sin_combinada"):
        motivo = combinada.get("motivo","")
        return (
            f"\U0001f6ab *Sin combinada {cuota_objetivo}x disponible*\n"
            f"{motivo}\n"
            f"Se necesitan picks con cuota individual suficiente para superar {cuota_objetivo}x en 3-4 picks."
        )

    bank = bank_actual or BANK_INICIAL
    stake = round(bank * STAKE_COMBINADA, 2)
    cuota_comb = combinada.get("cuota_combinada", 1.0)
    ganancia_pot = round(stake * (cuota_comb - 1), 2)

    subtipo = combinada.get("subtipo","").upper().replace("_ALTA","").replace("_4X","").replace("_5X","")
    n = combinada.get("n_picks", len(combinada.get("picks",[])))
    tipo_str = "CUADRUPLE" if n == 4 else "TRIPLE"
    ticket = combinada.get("ticket_id","")

    lineas = [
        f"\U0001f4b0 *COMB{int(cuota_objetivo)}X {tipo_str} {subtipo} — {combinada['fecha']}*",
        f"\U0001f39f `{ticket}`" if ticket else "",
        f"\U0001f4ca Score prom: {combinada.get('score_promedio','?')} | Riesgo prom: {combinada.get('riesgo_promedio','?')}",
    ]
    if combinada.get("n_prematch") is not None:
        lineas.append(f"\U0001f4cb {combinada.get('n_prematch',0)} prematch + {combinada.get('n_live',0)} live")
    lineas = [l for l in lineas if l]
    lineas.append("\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")

    for i, p in enumerate(combinada.get("picks",[]), 1):
        cuota_p = _cuota_segura(p)
        fuente = p.get("_fuente", p.get("tipo","prematch")).upper()
        minuto = p.get("minuto_consulta", p.get("minuto",""))
        extra = f" | Min:{minuto}'" if fuente == "LIVE" and minuto else ""
        hora_str = p.get("hora", p.get("hour",""))
        lineas.append(
            f"{i}. [{fuente}] *{p.get('partido','')}*{extra}\n"
            f"   \U0001f310 {p.get('country','')} | \U0001f3c6 {p.get('league','')} | \U0001f552 {hora_str}\n"
            f"   \U0001f3af {p.get('jugada','')}\n"
            f"   Score:{p.get('score','')} | Prob:{p.get('probabilidad',p.get('prob',''))}% | \U0001f4b0 Cuota:{cuota_p}"
        )

    lineas += [
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"\U0001f3af Cuota combinada: *{cuota_comb}x*",
        f"\U0001f4b0 Stake (10% bank): *S/ {stake:.2f}*",
        f"\U0001f4c8 Ganancia potencial: *S/ {ganancia_pot:.2f}*",
        f"\U0001f9e0 {combinada.get('razon_seleccion','')}",
    ]
    return "\n".join(lineas)


# ── Comandos /comb4 ──────────────────────────────────────────────────
async def comb4(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Combinada cuota 4x+ prematch."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f4b0 Armando combinada 4x+ prematch (3-4 picks)...")
    try:
        hoy = fecha_hoy_peru()
        comb = _armar_comb_alta("prematch", CUOTA_MIN_4X, CUOTA_MIN_PICK_4X, hoy)
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada 4x guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        await update.message.reply_text(_formato_comb_alta(comb, 4), parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")


async def comb4_live(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Combinada cuota 4x+ live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f534 Analizando partidos live para combinada 4x+...")
    try:
        hoy = fecha_hoy_peru()
        comb = _armar_comb_alta("live", CUOTA_MIN_4X, CUOTA_MIN_PICK_4X, hoy)
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada 4x live guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        await update.message.reply_text(_formato_comb_alta(comb, 4), parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")


async def comb4_mixta(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Combinada cuota 4x+ mixta prematch+live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f3af Armando combinada 4x+ mixta...")
    try:
        hoy = fecha_hoy_peru()
        comb = _armar_comb_alta("mixta_4x", CUOTA_MIN_4X, CUOTA_MIN_PICK_4X, hoy, mixta=True)
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada 4x mixta guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        await update.message.reply_text(_formato_comb_alta(comb, 4), parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")


# ── Comandos /comb5 ──────────────────────────────────────────────────
async def comb5(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Combinada cuota 5x+ prematch."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f4b0 Armando combinada 5x+ prematch (3-4 picks)...")
    try:
        hoy = fecha_hoy_peru()
        comb = _armar_comb_alta("prematch", CUOTA_MIN_5X, CUOTA_MIN_PICK_5X, hoy)
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada 5x guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        await update.message.reply_text(_formato_comb_alta(comb, 5), parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")


async def comb5_live(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Combinada cuota 5x+ live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f534 Analizando partidos live para combinada 5x+...")
    try:
        hoy = fecha_hoy_peru()
        comb = _armar_comb_alta("live", CUOTA_MIN_5X, CUOTA_MIN_PICK_5X, hoy)
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada 5x live guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        await update.message.reply_text(_formato_comb_alta(comb, 5), parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")


async def comb5_mixta(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Combinada cuota 5x+ mixta prematch+live."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("\U0001f3af Armando combinada 5x+ mixta...")
    try:
        hoy = fecha_hoy_peru()
        comb = _armar_comb_alta("mixta_5x", CUOTA_MIN_5X, CUOTA_MIN_PICK_5X, hoy, mixta=True)
        if comb and not comb.get("sin_combinada"):
            _guardar_combinada(comb)
            await update.message.reply_text(
                f"\u2705 Combinada 5x mixta guardada | Ticket: `{comb.get('ticket_id','')}`",
                parse_mode="Markdown"
            )
        await update.message.reply_text(_formato_comb_alta(comb, 5), parse_mode="Markdown")
    except Exception as e:
        await update.message.reply_text(f"\u274c Error: {e}")


# ─────────────────────────────────────────────
#  MODULO DE SELECCIONES NACIONALES
# ─────────────────────────────────────────────

# Ligas de selecciones nacionales detectables
LIGAS_SELECCIONES = {
    # FIFA
    "FIFA World Cup", "World Cup", "World Cup - Qualification",
    "World Cup - Qualification - CONMEBOL",
    "World Cup - Qualification - UEFA",
    "World Cup - Qualification - CAF",
    "World Cup - Qualification - AFC",
    "World Cup - Qualification - CONCACAF",
    "World Cup - Qualification - OFC",
    # Continentales
    "Copa America", "Copa América",
    "UEFA Nations League", "Nations League",
    "UEFA European Championship", "Euro",
    "Africa Cup of Nations", "AFCON",
    "Asian Cup", "AFC Asian Cup",
    "Gold Cup", "CONCACAF Gold Cup",
    "CONMEBOL", "Friendlies",
    "International Champions Cup",
    "International Friendlies",
    # Variantes comunes en la API
    "Friendlies - International",
    "World Cup - Qualification South America",
}

# Ranking FIFA aproximado (Top 50, actualizado mensualmente)
RANKING_FIFA = {
    "Argentina": 1, "France": 2, "England": 3, "Belgium": 4,
    "Brazil": 5, "Portugal": 6, "Netherlands": 7, "Spain": 8,
    "Morocco": 9, "Italy": 10, "Croatia": 11, "USA": 12,
    "Uruguay": 13, "Colombia": 14, "Mexico": 15, "Germany": 16,
    "Switzerland": 17, "Japan": 18, "Senegal": 19, "Denmark": 20,
    "Ecuador": 21, "Australia": 22, "Austria": 23, "South Korea": 24,
    "Hungary": 25, "Turkey": 26, "Ukraine": 27, "Poland": 28,
    "Sweden": 29, "Serbia": 30, "Peru": 31, "Chile": 32,
    "Paraguay": 33, "Venezuela": 34, "Bolivia": 35,
    "Costa Rica": 36, "Panama": 37, "Jamaica": 38,
    "Egypt": 39, "Nigeria": 40, "Ivory Coast": 41,
    "Cameroon": 42, "Ghana": 43, "Tunisia": 44,
    "Iran": 45, "Saudi Arabia": 46, "Qatar": 47,
    "New Zealand": 48, "Norway": 49, "Czech Republic": 50,
}

# Fases del torneo y sus caracteristicas
FASES_TORNEO = {
    "group": {
        "label": "Fase de Grupos",
        "mercados_preferidos": ["Under 2.5 goles", "Doble Oportunidad", "Under 3.5 goles"],
        "mercados_evitar": ["Ambos marcan - Si", "Over 2.5 goles"],
        "ajuste_score": 0,  # sin ajuste
        "nota": "Equipos especulan — menos goles, mas empates",
    },
    "round_of_16": {
        "label": "Octavos de Final",
        "mercados_preferidos": ["Tarjetas Over 3.5", "Corners Over 9.5", "Doble Oportunidad"],
        "mercados_evitar": [],
        "ajuste_score": 0.3,
        "nota": "Mayor tension — mas tarjetas y corners",
    },
    "quarter": {
        "label": "Cuartos de Final",
        "mercados_preferidos": ["Tarjetas Over 4.5", "Under 2.5 goles", "Corners Over 10.5"],
        "mercados_evitar": ["Ambos marcan - Si"],
        "ajuste_score": 0.5,
        "nota": "Alta tension — partidos cerrados",
    },
    "semi": {
        "label": "Semifinal",
        "mercados_preferidos": ["Under 2.5 goles", "Tarjetas Over 4.5", "1X o X2"],
        "mercados_evitar": ["Over 2.5 goles"],
        "ajuste_score": 0.7,
        "nota": "Maxima presion — muy pocos goles historicamente",
    },
    "final": {
        "label": "Final",
        "mercados_preferidos": ["Under 2.5 goles", "Tarjetas Over 5.5", "Under 3.5 goles"],
        "mercados_evitar": ["Over 2.5 goles", "Ambos marcan - Si"],
        "ajuste_score": 1.0,
        "nota": "Finales son cerradas — menos de 2.5 goles en 70% historico",
    },
    "friendly": {
        "label": "Amistoso",
        "mercados_preferidos": ["Over 2.5 goles", "Ambos marcan - Si", "Corners Over 9.5"],
        "mercados_evitar": [],
        "ajuste_score": -0.5,
        "nota": "Amistosos tienen mas goles — menor motivacion defensiva",
    },
}


def _detectar_fase_torneo(league_name, round_name=""):
    """Detecta la fase del torneo por el nombre de la liga y ronda."""
    league_l = (league_name or "").lower()
    round_l = (round_name or "").lower()

    if "friendly" in league_l or "amistoso" in league_l or "friendlies" in league_l:
        return "friendly"
    if "final" in round_l and "semi" not in round_l and "quarter" not in round_l:
        return "final"
    if "semi" in round_l:
        return "semi"
    if "quarter" in round_l or "cuarto" in round_l:
        return "quarter"
    if "round of 16" in round_l or "octavo" in round_l or "1/8" in round_l:
        return "round_of_16"
    if "group" in round_l or "grupo" in round_l or "matchday" in round_l:
        return "group"
    # Por defecto grupos si es eliminatoria o copa
    if any(x in league_l for x in ["qualification", "eliminatoria", "world cup", "copa"]):
        return "group"
    return "group"


def _es_partido_selecciones(league_name, country=""):
    """Detecta si un partido es de selecciones nacionales."""
    if not league_name:
        return False
    for liga in LIGAS_SELECCIONES:
        if liga.lower() in league_name.lower():
            return True
    # Detectar por patron: si la liga contiene "Qualification" o "Nations"
    league_l = league_name.lower()
    if any(x in league_l for x in ["qualification", "nations league", "copa america",
                                     "world cup", "euro 20", "gold cup", "friendl"]):
        return True
    return False


def analizar_seleccion(fixture_id, home, away, league, country, hora, round_name=""):
    """
    Analiza un partido de selecciones con criterios especificos:
    - Ranking FIFA, fase del torneo, efecto sede
    - H2H historico, forma reciente
    - Motivacion (necesita ganar vs le sirve empate)
    - Cansancio acumulado (dias desde ultimo partido)
    - Estilo tactico historico (defensivo vs ofensivo)
    - Lesionados y suspendidos de la convocatoria
    - Clima y altitud del estadio
    - Estadisticas historicas de mundiales por fase
    Score umbral: 8.0+ (mas conservador que clubes)
    """
    fase = _detectar_fase_torneo(league, round_name)
    config_fase = FASES_TORNEO.get(fase, FASES_TORNEO["group"])

    # Ranking FIFA
    rank_home = RANKING_FIFA.get(home, 60)
    rank_away = RANKING_FIFA.get(away, 60)
    diff_ranking = rank_away - rank_home  # positivo = local mejor rankeado

    # Datos via API
    fixture_data = api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)
    if not fixture_data:
        return None

    fx = fixture_data[0]
    home_id = fx["teams"]["home"]["id"]
    away_id = fx["teams"]["away"]["id"]
    venue = fx["fixture"]["venue"] or {}
    sede = venue.get("city","")
    # Altitud aproximada de ciudades sedes conocidas (metros)
    ALTITUDES = {
        "La Paz": 3600, "Quito": 2850, "Bogota": 2600,
        "Mexico City": 2240, "Guadalajara": 1560,
        "Denver": 1609, "Calgary": 1045,
    }
    altitud = ALTITUDES.get(sede, 0)

    # H2H de los ultimos 8 enfrentamientos
    h2h = api_get(f"/fixtures/headtohead?h2h={home_id}-{away_id}&last=8",
                   use_cache=True, ttl=7200)
    h2h_home_wins = 0
    h2h_away_wins = 0
    h2h_empates = 0
    goles_h2h = []
    home_marca_primero = 0
    if h2h:
        for m in h2h:
            gh = m["goals"]["home"] or 0
            ga = m["goals"]["away"] or 0
            goles_h2h.append(gh + ga)
            winner_home = m["teams"]["home"]["winner"]
            if winner_home is True: h2h_home_wins += 1
            elif winner_home is False: h2h_away_wins += 1
            else: h2h_empates += 1
    goles_h2h_prom = round(sum(goles_h2h)/len(goles_h2h), 2) if goles_h2h else 2.5

    # Forma reciente y cansancio (ultimos 5 partidos)
    home_fixtures = api_get(f"/fixtures?team={home_id}&last=5", use_cache=True, ttl=3600)
    away_fixtures = api_get(f"/fixtures?team={away_id}&last=5", use_cache=True, ttl=3600)

    def calcular_forma_y_cansancio(fixtures, team_id):
        puntos = 0
        dias_descanso = 99
        goles_favor = []
        goles_contra = []
        for m in (fixtures or []):
            es_local = m["teams"]["home"]["id"] == team_id
            winner = m["teams"]["home"]["winner"] if es_local else m["teams"]["away"]["winner"]
            if winner is True: puntos += 3
            elif winner is None: puntos += 1
            gh = m["goals"]["home"] or 0
            ga = m["goals"]["away"] or 0
            gf = gh if es_local else ga
            gc = ga if es_local else gh
            goles_favor.append(gf)
            goles_contra.append(gc)
            # Dias desde ese partido
            try:
                from datetime import datetime as _dt3, date as _d3
                fecha_m = m["fixture"]["date"][:10]
                dias = (_d3.today() - _dt3.strptime(fecha_m, "%Y-%m-%d").date()).days
                if dias < dias_descanso:
                    dias_descanso = dias
            except Exception:
                pass
        gf_prom = round(sum(goles_favor)/len(goles_favor), 2) if goles_favor else 1.0
        gc_prom = round(sum(goles_contra)/len(goles_contra), 2) if goles_contra else 1.0
        return puntos, dias_descanso, gf_prom, gc_prom

    forma_home, desc_home, gf_home, gc_home = calcular_forma_y_cansancio(home_fixtures, home_id)
    forma_away, desc_away, gf_away, gc_away = calcular_forma_y_cansancio(away_fixtures, away_id)

    # Lesionados y suspendidos de la convocatoria
    injuries = api_get(f"/injuries?fixture={fixture_id}", use_cache=True, ttl=3600)
    bajas_home = sum(1 for p in (injuries or [])
                     if p.get("team",{}).get("id") == home_id) if injuries else 0
    bajas_away = sum(1 for p in (injuries or [])
                     if p.get("team",{}).get("id") == away_id) if injuries else 0

    # Estilo tactico: goles a favor vs contra
    # Ofensivo: gf_prom > 1.8 | Defensivo: gc_prom < 0.8
    estilo_home = "ofensivo" if gf_home > 1.8 else ("defensivo" if gc_home < 0.8 else "mixto")
    estilo_away = "ofensivo" if gf_away > 1.8 else ("defensivo" if gc_away < 0.8 else "mixto")

    # ── SCORING ──────────────────────────────────────────────────────
    score_base = 5.0

    # 1. Factor ranking FIFA (max +2.0)
    if diff_ranking >= 20:
        score_base += 2.0
    elif diff_ranking >= 10:
        score_base += 1.5
    elif diff_ranking >= 5:
        score_base += 1.0
    elif diff_ranking <= -20:
        score_base += 0.5
    else:
        score_base += 0.8

    # 2. Factor H2H (max +1.5)
    total_h2h = h2h_home_wins + h2h_away_wins + h2h_empates
    if total_h2h > 0:
        if h2h_home_wins / total_h2h >= 0.6:
            score_base += 1.5
        elif h2h_home_wins / total_h2h >= 0.4:
            score_base += 1.0
        else:
            score_base += 0.5

    # 3. Factor forma (max +1.0)
    if forma_home >= 12:
        score_base += 1.0
    elif forma_home >= 9:
        score_base += 0.7
    else:
        score_base += 0.3

    # 4. Ajuste por fase
    score_base += config_fase["ajuste_score"]

    # 5. Efecto sede (+0.5 si juega en casa)
    if sede:
        score_base += 0.5

    # 6. Cansancio: si jugaron hace menos de 4 dias (-0.3)
    if desc_home < 4:
        score_base -= 0.3
    if desc_away < 4:
        score_base += 0.2  # visitante cansado = ventaja local

    # 7. Bajas importantes (-0.2 por cada 2 bajas)
    if bajas_home >= 2:
        score_base -= round(bajas_home * 0.1, 1)
    if bajas_away >= 2:
        score_base += round(bajas_away * 0.1, 1)

    # 8. Altitud (si > 2000m penaliza al visitante +0.3)
    if altitud > 2000:
        score_base += 0.3

    score_final = round(min(10.0, max(5.0, score_base)), 1)

    # ── PROBABILIDADES HISTORICAS POR FASE ───────────────────────────
    # Under 2.5: grupos 59%, octavos 62%, cuartos 65%, semis 70%, final 68%
    PROB_UNDER25_FASE = {
        "group": 59, "round_of_16": 62, "quarter": 65,
        "semi": 70, "final": 68, "friendly": 45,
    }
    prob_under25_base = PROB_UNDER25_FASE.get(fase, 59)
    # Ajuste por estilos defensivos
    if estilo_home == "defensivo" and estilo_away == "defensivo":
        prob_under25_base += 8
    elif estilo_home == "defensivo" or estilo_away == "defensivo":
        prob_under25_base += 4
    if goles_h2h_prom < 2.0:
        prob_under25_base += 5
    elif goles_h2h_prom > 3.0:
        prob_under25_base -= 8

    # Motivacion: en grupos si ambos clasificados puede haber menos intensidad
    es_motivacion_alta = fase in ("round_of_16","quarter","semi","final")

    # ── SUGERENCIAS POR MERCADO ──────────────────────────────────────
    sugerencias = []
    mercados_pref = config_fase["mercados_preferidos"]
    mercados_evitar = config_fase["mercados_evitar"]

    # Under 2.5 goles (con probabilidad ajustada por fase y estilos)
    if "Under 2.5 goles" in mercados_pref and "Under 2.5 goles" not in mercados_evitar:
        prob_u25 = min(85, prob_under25_base)
        sugerencias.append({
            "mercado": "Goles",
            "jugada": "Under 2.5 goles",
            "prob": prob_u25,
            "score": score_final,
            "riesgo": 1.5,
            "cuota_minima": cuota_minima(prob_u25/100, 1.5),
            "cuota": cuota_minima(prob_u25/100, 1.5),
            "confianza": etiqueta_confianza(score_final),
            "motivo": f"Fase {config_fase['label']} — hist {prob_under25_base}% Under 2.5",
        })

    # Under 3.5 goles
    if "Under 3.5 goles" in mercados_pref:
        prob_u35 = min(88, prob_under25_base + 14)
        sugerencias.append({
            "mercado": "Goles",
            "jugada": "Under 3.5 goles",
            "prob": prob_u35,
            "score": score_final,
            "riesgo": 1.2,
            "cuota_minima": cuota_minima(prob_u35/100, 1.2),
            "cuota": cuota_minima(prob_u35/100, 1.2),
            "confianza": etiqueta_confianza(score_final),
            "motivo": f"Partidos cerrados — {estilo_home} vs {estilo_away}",
        })

    # Doble Oportunidad (ajustada por ranking y motivacion)
    if "Doble Oportunidad" in mercados_pref or "1X o X2" in mercados_pref:
        if diff_ranking >= 10:
            jugada_do = "1X"
            prob_do = 80 if es_motivacion_alta else 73
        elif diff_ranking <= -10:
            jugada_do = "X2"
            prob_do = 74 if es_motivacion_alta else 67
        else:
            jugada_do = "1X"
            prob_do = 65
        # Ajuste por cansancio del visitante
        if desc_away < 4:
            prob_do = min(85, prob_do + 5)
        sugerencias.append({
            "mercado": "Doble Oportunidad",
            "jugada": jugada_do,
            "prob": prob_do,
            "score": score_final,
            "riesgo": 1.3,
            "cuota_minima": cuota_minima(prob_do/100, 1.3),
            "cuota": cuota_minima(prob_do/100, 1.3),
            "confianza": etiqueta_confianza(score_final),
            "motivo": f"Ranking diff: {diff_ranking} | Descanso visitante: {desc_away} dias",
        })

    # TARJETAS ELIMINADO tambien para selecciones: dependen del arbitro y
    # del animo de los jugadores, factores que el modelo no mide.

    # Corners (equipos ofensivos generan mas corners)
    if any("Corner" in m for m in mercados_pref):
        corner_jugada = next((m for m in mercados_pref if "Corner" in m), "Corners Over 9.5")
        prob_corner = 60
        if estilo_home == "ofensivo" or estilo_away == "ofensivo":
            prob_corner += 8
        if diff_ranking >= 15:
            prob_corner += 5  # equipo dominante genera mas corners
        sugerencias.append({
            "mercado": "Corners",
            "jugada": corner_jugada,
            "prob": prob_corner,
            "score": round(score_final - 0.3, 1),
            "riesgo": 2.0,
            "cuota_minima": cuota_minima(prob_corner/100, 2.0),
            "cuota": cuota_minima(prob_corner/100, 2.0),
            "confianza": etiqueta_confianza(score_final - 0.3),
            "motivo": f"Estilo: {estilo_home} vs {estilo_away}",
        })

    # Amistosos: Over 2.5 (menos presion = mas goles)
    if fase == "friendly":
        prob_over = 55 if goles_h2h_prom >= 2.5 else 42
        sugerencias.append({
            "mercado": "Goles",
            "jugada": "Over 2.5 goles",
            "prob": prob_over,
            "score": round(score_final - 0.5, 1),
            "riesgo": 2.0,
            "cuota_minima": cuota_minima(prob_over/100, 2.0),
            "cuota": cuota_minima(prob_over/100, 2.0),
            "confianza": etiqueta_confianza(score_final - 0.5),
            "motivo": f"Amistoso — menor presion defensiva | H2H prom: {goles_h2h_prom} goles",
        })

    # Filtrar score >= 8.0
    sugerencias = [s for s in sugerencias if s["score"] >= 8.0]
    sugerencias.sort(key=lambda x: x["score"], reverse=True)

    if not sugerencias:
        return None

    # Nota de alerta por factores de riesgo
    alertas = []
    if bajas_home >= 3:
        alertas.append(f"{home} tiene {bajas_home} bajas")
    if bajas_away >= 3:
        alertas.append(f"{away} tiene {bajas_away} bajas")
    if desc_home < 4:
        alertas.append(f"{home} jugo hace {desc_home} dias")
    if altitud > 2000:
        alertas.append(f"Altitud {altitud}m — afecta al visitante")

    return {
        "fixture_id": fixture_id,
        "partido": f"{home} vs {away}",
        "home": home,
        "away": away,
        "league": league,
        "country": country,
        "hora": hora,
        "tipo": "seleccion",
        "fase": config_fase["label"],
        "fase_key": fase,
        "rank_home": rank_home,
        "rank_away": rank_away,
        "diff_ranking": diff_ranking,
        "h2h_home_wins": h2h_home_wins,
        "h2h_away_wins": h2h_away_wins,
        "h2h_empates": h2h_empates,
        "goles_h2h_prom": goles_h2h_prom,
        "forma_home": forma_home,
        "forma_away": forma_away,
        "desc_home": desc_home,
        "desc_away": desc_away,
        "bajas_home": bajas_home,
        "bajas_away": bajas_away,
        "estilo_home": estilo_home,
        "estilo_away": estilo_away,
        "altitud": altitud,
        "score": sugerencias[0]["score"],
        "sugerencias": sugerencias,
        "nota_fase": config_fase["nota"],
        "alertas": alertas,
        "mercados_evitar": mercados_evitar,
    }


# ─────────────────────────────────────────────
#  /estado — Dashboard diario
#  Alertas automaticas de picks con edge EXCELENTE
# ─────────────────────────────────────────────

async def estado(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /estado — Dashboard rapido con todo lo importante del dia.
    Bank acumulado, combinadas activas, efectividad semanal, mejor mercado.
    """
    _registrar_chat_alarma(update.effective_chat.id)
    hoy = fecha_hoy_peru()
    hora_actual = fecha_hora_peru()

    # ── Bank acumulado del mes ───────────────────────────────────────
    historial = _actualizar_bank_acumulado()
    if historial and len(historial) >= 2:
        bank_actual = historial[-1].get("bank", BANK_INICIAL)
        resultado_mes = round(bank_actual - BANK_INICIAL, 2)
        roi_mes = round(resultado_mes / BANK_INICIAL * 100, 2)
        ops_mes = len([h for h in historial if h.get("estado")])
        bank_str = f"S/ {bank_actual:.2f} ({roi_mes:+.1f}% ROI)"
        bank_emoji = "\U0001f4c8" if resultado_mes >= 0 else "\U0001f4c9"
    else:
        bank_actual = BANK_INICIAL
        bank_str = f"S/ {BANK_INICIAL:.2f} (sin operaciones)"
        bank_emoji = "\U0001f4b0"
        ops_mes = 0

    # ── Picks de hoy ────────────────────────────────────────────────
    picks_todos = leer_json(PICKS_FILE)
    picks_hoy = [p for p in picks_todos
                 if (p.get("fecha_partido") or p.get("fecha",""))[:10] == hoy]
    total_hoy = len(picks_hoy)
    aciertos_hoy = sum(1 for p in picks_hoy if p.get("estado","").lower()=="acierto")
    fallos_hoy = sum(1 for p in picks_hoy if p.get("estado","").lower()=="fallo")
    pendientes_hoy = total_hoy - aciertos_hoy - fallos_hoy
    cerrados_hoy = aciertos_hoy + fallos_hoy
    ef_hoy = round(aciertos_hoy/cerrados_hoy*100,1) if cerrados_hoy > 0 else None

    # ── Efectividad semanal ──────────────────────────────────────────
    from datetime import timedelta as _td_est
    hace7 = (fecha_peru_obj() - _td_est(days=7)).strftime("%Y-%m-%d")
    picks_semana = [p for p in picks_todos
                    if (p.get("fecha_partido") or p.get("fecha",""))[:10] >= hace7
                    and p.get("estado","").lower() in ("acierto","fallo")]
    ac_sem = sum(1 for p in picks_semana if p.get("estado","").lower()=="acierto")
    ef_sem = round(ac_sem/len(picks_semana)*100,1) if picks_semana else None

    # ── Mejor mercado de hoy ─────────────────────────────────────────
    mercados_hoy = {}
    for p in picks_hoy:
        if p.get("estado","").lower() not in ("acierto","fallo"):
            continue
        jugada = p.get("jugada","Otro")
        if "Corner" in jugada: m = "Corners"
        elif "gol" in jugada.lower(): m = "Goles"
        elif "Tarjeta" in jugada: m = "Tarjetas"
        elif "BTTS" in jugada or "Ambos" in jugada: m = "BTTS"
        elif "1X" in jugada or "X2" in jugada: m = "Doble Op."
        else: m = "Otro"
        if m not in mercados_hoy:
            mercados_hoy[m] = {"a":0,"t":0}
        mercados_hoy[m]["t"] += 1
        if p.get("estado","").lower()=="acierto":
            mercados_hoy[m]["a"] += 1

    mejor_mercado = max(
        mercados_hoy.items(),
        key=lambda x: x[1]["a"]/x[1]["t"] if x[1]["t"] else 0
    ) if mercados_hoy else None

    # ── Combinadas activas ───────────────────────────────────────────
    combinadas = leer_json(COMBINADAS_FILE)
    combs_hoy = [c for c in combinadas
                 if c.get("fecha","")[:10] == hoy
                 and not c.get("sin_combinada")
                 and c.get("picks")]
    combs_pendientes = [c for c in combs_hoy if c.get("estado","pendiente").lower()=="pendiente"]
    combs_acierto = sum(1 for c in combs_hoy if c.get("estado","").lower()=="acierto")
    combs_fallo = sum(1 for c in combs_hoy if c.get("estado","").lower()=="fallo")

    # ── Picks con edge EXCELENTE pendientes ─────────────────────────
    picks_valor = [p for p in picks_hoy
                   if p.get("edge_categoria") in ("EXCELENTE","BUENO")
                   and p.get("estado","pendiente").lower() == "pendiente"
                   and not _es_btts(p)]  # BTTS excluido temporalmente

    # ── Armar mensaje ────────────────────────────────────────────────
    lineas = [
        f"\U0001f4ca *ESTADO — {hoy} | {hora_actual}*",
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"{bank_emoji} *Bank del mes:* {bank_str}",
        f"\U0001f4b0 Stake siguiente: S/ {round(bank_actual*STAKE_COMBINADA,2):.2f} (10%)",
        f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
        f"\U0001f3af *Picks de hoy:* {total_hoy} total",
        f"\u2705 {aciertos_hoy} aciertos | \u274c {fallos_hoy} fallos | \u23f3 {pendientes_hoy} pendientes",
        f"Efectividad hoy: *{ef_hoy}%*" if ef_hoy else "Sin picks cerrados hoy",
        f"Efectividad 7 dias: *{ef_sem}%* ({len(picks_semana)} cerrados)" if ef_sem else "Sin datos semanales",
    ]

    if mejor_mercado:
        m_nom, m_dat = mejor_mercado
        ef_m = round(m_dat["a"]/m_dat["t"]*100,1)
        lineas.append(f"\U0001f3c6 Mejor mercado hoy: *{m_nom}* ({ef_m}%)")

    lineas.append(f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")

    # Combinadas
    lineas.append(
        f"\U0001f3af *Combinadas hoy:* {len(combs_hoy)} | "
        f"\u2705 {combs_acierto} | \u274c {combs_fallo} | \u23f3 {len(combs_pendientes)}"
    )

    for c in combs_pendientes[:3]:  # max 3
        n = c.get("n_picks", len(c.get("picks",[])))
        subtipo = c.get("subtipo","?").upper().replace("_ALTA","")
        ticket = c.get("ticket_id","")[-8:] if c.get("ticket_id") else "?"
        lineas.append(
            f"  \u23f3 [{subtipo}] {n} picks | {c.get('cuota_combinada','?')}x | `{ticket}`"
        )

    if len(combs_pendientes) > 3:
        lineas.append(f"  ...y {len(combs_pendientes)-3} mas")

    # Picks con valor vs Pinnacle
    if picks_valor:
        lineas.append(f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")
        lineas.append(f"\U0001f4b9 *Picks con valor vs Pinnacle ({len(picks_valor)}):*")
        for p in picks_valor[:3]:
            edge_p = p.get("edge","?")
            lineas.append(
                f"  \u2605 {p.get('partido','')}\n"
                f"    {p.get('jugada','')} | Edge: +{edge_p}% | Cuota: {_cuota_segura(p)}"
            )

    lineas.append(f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")
    lineas.append(f"Operaciones del mes: {ops_mes} combinadas")

    await update.message.reply_text("\n".join(lineas), parse_mode="Markdown")


async def _alerta_edge_excelente_job(context):
    """
    Job cada 30 minutos: detecta picks nuevos con edge EXCELENTE vs Pinnacle
    y notifica automaticamente al usuario sin que tenga que llamar ningun comando.
    """
    hoy = fecha_hoy_peru()
    picks_todos = leer_json(PICKS_FILE)

    picks_excelentes = [
        p for p in picks_todos
        if (p.get("fecha_partido") or p.get("fecha",""))[:10] == hoy
        and p.get("edge_categoria") == "EXCELENTE"
        and p.get("estado","pendiente").lower() == "pendiente"
        and not p.get("alerta_edge_enviada")
        and p.get("edge") is not None
        and float(p.get("edge",0)) >= 10
        and not _es_btts(p)  # BTTS excluido hasta mejorar efectividad
    ]

    if not picks_excelentes:
        return

    for chat_id in _CHAT_IDS_ALARMAS:
        try:
            lineas = [
                f"\U0001f4b9 *ALERTA — Pick con valor EXCELENTE vs Pinnacle*",
                f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501",
            ]
            for p in picks_excelentes:
                cuota_p = _cuota_segura(p)
                edge_p = p.get("edge","?")
                lineas.append(
                    f"\u2605 *{p.get('partido','')}*\n"
                    f"   \U0001f310 {p.get('country','')} | {p.get('league','')}\n"
                    f"   \U0001f3af {p.get('jugada','')}\n"
                    f"   Score: {p.get('score','')} | Cuota Pinnacle: {cuota_p}\n"
                    f"   \U0001f4b9 *Edge: +{edge_p}% vs Pinnacle* [EXCELENTE]\n"
                    f"   Prob modelo: {p.get('probabilidad',p.get('prob','?'))}% | "
                    f"Prob implicita Pinnacle: {round(100/cuota_p,1) if cuota_p else '?'}%"
                )
            lineas.append(f"\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501")
            lineas.append(f"\u23f0 {p.get('hora','')} | Considera incluirlo en combinadas")

            await context.bot.send_message(
                chat_id=chat_id,
                text="\n".join(lineas),
                parse_mode="Markdown"
            )
        except Exception:
            pass

    # Marcar como alertados para no repetir
    for p in picks_excelentes:
        p["alerta_edge_enviada"] = True
    guardar_json_lista(PICKS_FILE, picks_todos)

app = ApplicationBuilder().token(TELEGRAM_TOKEN).build()

app.add_handler(CommandHandler("start", start))
app.add_handler(CommandHandler("analizar", analizar))
app.add_handler(CommandHandler("detalle", detalle))
app.add_handler(CommandHandler("top", top))
app.add_handler(CommandHandler("top_manana", top_manana))
app.add_handler(CommandHandler("elite", elite))
app.add_handler(CommandHandler("elite_manana", elite_manana))
app.add_handler(CommandHandler("fixtures", fixtures))
app.add_handler(CommandHandler("fixtures_manana", fixtures_manana))
app.add_handler(CommandHandler("scanear", scanear))
app.add_handler(CommandHandler("alertas_on", alertas_on))
app.add_handler(CommandHandler("alertas_off", alertas_off))
app.add_handler(CommandHandler("resumen", resumen))
app.add_handler(CommandHandler("resumen_ayer", resumen_ayer))
app.add_handler(CommandHandler("resumentop", resumentop))
app.add_handler(CommandHandler("resumentoplive", resumentoplive))
app.add_handler(CommandHandler("pdf_semana", pdf_semana))
app.add_handler(CommandHandler("pdf_mes", pdf_mes))
app.add_handler(CommandHandler("feedback", feedback))
app.add_handler(CommandHandler("rendimiento", rendimiento))
app.add_handler(CommandHandler("combinada", combinada))
app.add_handler(CommandHandler("combinada_live", combinada_live))
app.add_handler(CommandHandler("combinada_mixta", combinada_mixta))
app.add_handler(CommandHandler("comb3", comb3))
app.add_handler(CommandHandler("comb3_live", comb3_live))
app.add_handler(CommandHandler("comb3_mixta", comb3_mixta))
app.add_handler(CommandHandler("comb4", comb4))
app.add_handler(CommandHandler("comb4_live", comb4_live))
app.add_handler(CommandHandler("comb4_mixta", comb4_mixta))
app.add_handler(CommandHandler("comb5", comb5))
app.add_handler(CommandHandler("comb5_live", comb5_live))
app.add_handler(CommandHandler("comb5_mixta", comb5_mixta))
app.add_handler(CommandHandler("reparar_cuotas", reparar_cuotas))
app.add_handler(CommandHandler("actualizar_combinadas", actualizar_combinadas_cmd))
app.add_handler(CommandHandler("resumen_prematch", resumen_prematch))
app.add_handler(CommandHandler("resumen_live", resumen_live))
app.add_handler(CommandHandler("resumen_combinadas", resumen_combinadas))
app.add_handler(CommandHandler("estado", estado))
app.add_handler(CommandHandler("escalera", escalera))
app.add_handler(CommandHandler("confirmar_escalera", confirmar_escalera))
app.add_handler(CommandHandler("cancelar_escalera", cancelar_escalera))
app.add_handler(CommandHandler("analizar_all", analizar_all))
app.add_handler(CommandHandler("live_all", live_all))

print("🤖 HarryNine V14 ejecutándose...")
async def _set_commands(app_instance):
    from telegram import BotCommand
    comandos = [
        BotCommand("start",                     "Inicio y menu completo"),
        BotCommand("analizar_all",              "Analiza TODAS las ligas auto"),
        BotCommand("analizar",                  "Analiza partido por ID"),
        BotCommand("detalle",                   "Detalle completo partido"),
        BotCommand("fixtures",                  "Partidos hoy todas ligas"),
        BotCommand("fixtures_manana",           "Partidos manana"),
        BotCommand("top",                       "Picks TOP hoy 7.5+"),
        BotCommand("elite",                     "Picks ELITE hoy 9.0+"),
        BotCommand("top_manana",                "Picks TOP manana"),
        BotCommand("elite_manana",              "Picks ELITE manana"),
        BotCommand("live_all",                  "Analiza TODOS los partidos live"),
        BotCommand("alertas_on",                "Activar alertas live"),
        BotCommand("alertas_off",               "Desactivar alertas"),
        BotCommand("combinada",                 "Combinada optima prematch del dia"),
        BotCommand("combinada_live",            "Combinada optima con picks live"),
        BotCommand("combinada_mixta",           "Combinada mixta prematch + live"),
        BotCommand("scanear",                   "Escanea todas las ligas"),
        BotCommand("resumen",                   "Resumen PDF del dia"),
        BotCommand("resumen_ayer",              "Resumen de ayer + combinadas"),
        BotCommand("resumentop",                "PDF picks prematch"),
        BotCommand("resumentoplive",            "PDF picks live"),
        BotCommand("pdf_semana",                "Reporte semanal PDF"),
        BotCommand("pdf_mes",                   "Reporte mensual PDF"),
        BotCommand("rendimiento",               "Rendimiento y bank"),
        BotCommand("feedback",                  "Marcar resultado pick"),
        BotCommand("actualizar_combinadas",     "Fuerza actualizar resultados combinadas"),
    ]
    await app_instance.bot.set_my_commands(comandos)

# Registrar comandos via post_init usando el job_queue al arrancar
async def _registrar_comandos_bot(context):
    from telegram import BotCommand
    comandos = [
        BotCommand("start",                      "Inicio y menu completo"),
        BotCommand("analizar_all",               "Analiza TODAS las ligas auto"),
        BotCommand("analizar",                   "Analiza partido por ID"),
        BotCommand("detalle",                    "Detalle completo partido"),
        BotCommand("fixtures",                   "Partidos hoy todas ligas"),
        BotCommand("fixtures_manana",            "Partidos manana"),
        BotCommand("top",                        "Picks TOP hoy 7.5+"),
        BotCommand("elite",                      "Picks ELITE hoy 9.0+"),
        BotCommand("top_manana",                 "Picks TOP manana"),
        BotCommand("elite_manana",               "Picks ELITE manana"),
        BotCommand("live_all",                   "Analiza TODOS los partidos live"),
        BotCommand("alertas_on",                 "Activar alertas live"),
        BotCommand("alertas_off",                "Desactivar alertas"),
        BotCommand("combinada",                  "Combinada optima prematch"),
        BotCommand("combinada_live",             "Combinada optima live"),
        BotCommand("combinada_mixta",            "Combinada mixta prematch+live"),
        BotCommand("comb3",                      "Combinada 3x+ prematch"),
        BotCommand("comb3_live",                 "Combinada 3x+ live"),
        BotCommand("comb3_mixta",                "Combinada 3x+ mixta"),
        BotCommand("comb4",                      "Combinada 4x+ prematch"),
        BotCommand("comb4_live",                 "Combinada 4x+ live"),
        BotCommand("comb4_mixta",                "Combinada 4x+ mixta"),
        BotCommand("comb5",                      "Combinada 5x+ prematch"),
        BotCommand("comb5_live",                 "Combinada 5x+ live"),
        BotCommand("comb5_mixta",                "Combinada 5x+ mixta"),
        BotCommand("scanear",                    "Escanea todas las ligas"),
        BotCommand("resumen",                    "Resumen PDF del dia"),
        BotCommand("resumen_ayer",               "Resumen de ayer + combinadas"),
        BotCommand("resumen_prematch",           "Resumen diario solo prematch"),
        BotCommand("resumen_live",               "Resumen diario solo live"),
        BotCommand("resumen_combinadas",         "Resumen diario de combinadas"),
        BotCommand("estado",                     "Dashboard rapido del dia"),
        BotCommand("escalera",                   "Arma escalera cronologica de picks"),
        BotCommand("confirmar_escalera",         "Confirma la escalera propuesta"),
        BotCommand("cancelar_escalera",          "Cancela la escalera activa"),
        BotCommand("resumentop",                 "PDF picks prematch"),
        BotCommand("resumentoplive",             "PDF picks live"),
        BotCommand("pdf_semana",                 "Reporte semanal PDF"),
        BotCommand("pdf_mes",                    "Reporte mensual PDF"),
        BotCommand("rendimiento",                "Rendimiento y bank"),
        BotCommand("feedback",                   "Marcar resultado pick"),
    ]
    try:
        await context.bot.set_my_commands(comandos)
    except Exception:
        pass

app.job_queue.run_once(_registrar_comandos_bot, when=3)

# Job GLOBAL de alertas live: uno solo para todos los suscriptores.
# Se registra siempre al arrancar; si no hay suscriptores el job retorna
# de inmediato sin gastar llamadas a la API.
app.job_queue.run_repeating(
    revisar_alertas_live,
    interval=ALERTAS_INTERVALO,
    first=20,
    name="alertas_live_global",
)

app.run_polling()