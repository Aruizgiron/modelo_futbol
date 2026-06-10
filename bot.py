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
from typing import Optional, List, Dict, Tuple, Any
import json
import time
import asyncio
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

# ════════════════════════════════════════════════════════════════════════════
# MÓDULO DE MEJORAS V15 — Integrado directamente
# Investigación sesiones 1-4: selectividad, regresión a la media, CLV,
# criterios por mercado, ajustes mundiales, calibración, 3 niveles de stake.
# ════════════════════════════════════════════════════════════════════════════
import math as _math_mejoras
from collections import defaultdict as _defaultdict_mejoras

"""
HarryNine V15 — Módulo de Mejoras
==================================
Implementa TODAS las recomendaciones de investigación de las sesiones 1-4.

CÓMO INTEGRAR AL BOT:
    Al inicio de bot.py, después de los imports, añadir:
        from harrynine_mejoras_v15 import *

    Luego aplicar los parches de constantes y llamadas descritos al final
    de este archivo en la sección ## INSTRUCCIONES DE INTEGRACIÓN.

Grupos implementados:
  - Bugs B1, B2 (cuotas reales + veto discrepancia)
  - Constantes mini-tickets corregidas (CQ1)
  - Selectividad radical: MAX_PICKS_DIA reducido, score mínimo subido
  - Veto victoria visitante directa en ligas top
  - xPTS gap + regresión a la media (X1-X4)
  - Eficiencia ofensiva (X3-X4)
  - Tabla AH completa diff xG → línea (Z11-Z15, P13)
  - Combined % como criterio O/U 2.5 (Z1-Z6)
  - Criterios DC refinados (Z7-Z10)
  - Criterios Corners refinados (Z16-Z20)
  - Criterios Over 1.5 mejorados (Z21-Z25)
  - Criterios O/U 3.5 propios (Z26-Z29)
  - Ajustes calor/altitud Mundial 2026 (X5-X7, X14-X15, N4-N7)
  - Eficiencia de mercado por liga (X13, Y9)
  - CLV tracking en aprendizaje.json (N3)
  - 3 niveles de stake por score (P9)
  - Veto DC cuota < 1.25 (Z7)
  - Empate directo como mercado (P10, P15)
  - Shots concedidos como proxy pressing (X9-X10, Y1-Y3)
  - Set piece rate flag (X8, Y7)
  - Lesión flag: cuota sube >8% en 2h (X11-X12)
  - Ajuste Rolling 3 partidos (Z5)
  - Liga eficiencia → umbral dinámico confluencia (X13, Y9)
"""

# (json, os, datetime ya importados arriba)

# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 1 — CONSTANTES CORREGIDAS
# Reemplazar las originales del bot con estos valores
# ─────────────────────────────────────────────────────────────────────────────

# ── MINI-TICKETS: corrección de EV mínimo ────────────────────────────────────
# Investigación: EV positivo requiere cuota ≥ 1.19 para que el margen no se coma
# la ganancia. Cuota objetivo sube a 1.80-2.50 para EV real compuesto.
MINI_TICKET_CUOTA_MIN      = 1.19   # antes: 1.10
MINI_TICKET_CUOTA_MAX      = 1.80   # sin cambio
MINI_TICKET_CUOTA_OBJ_MIN  = 1.80   # antes: 1.40  ← crítico
MINI_TICKET_CUOTA_OBJ_MAX  = 2.50   # antes: 2.20
MINI_TICKET_PROB_MIN       = 60.0   # dinámico: max(60, 103/cuota) aplicado en función
MINI_TICKET_MAX_DIA        = 3      # antes: 5 — selectividad radical

# ── PICKS GENERALES: selectividad radical ────────────────────────────────────
# Investigación: reducir volumen de 8 a 3 picks/día de alta calidad
# sube el win rate global 6-10%. Solo picks con múltiples señales convergentes.
MAX_PICKS_DIA_V15          = 4      # antes: 8
SCORE_MIN_GLOBAL_V15       = 8.5    # antes: implícito 7.0-7.5

# ── SCORE MÍNIMO POR CUOTA (actualizado) ─────────────────────────────────────
SCORE_MIN_POR_CUOTA_V15 = [
    (1.50, 2.20, 8.0),   # antes: 7.5 — sube para filtrar picks débiles
    (2.21, 3.00, 8.5),   # antes: 8.0
    (3.01, 99.0, 9.0),   # antes: 8.5
]

# ── COMBINADAS: umbral de score mínimo ───────────────────────────────────────
COMB_SCORE_MIN_V15         = 8.0    # antes: 7.5
COMB_SCORE_MIN_OVER15_V15  = 8.5    # antes: 8.0

# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 2 — MAPA DE EFICIENCIA DE MERCADO POR LIGA
# Determina cuántas señales confluentes se necesitan para generar un pick.
# Liga muy eficiente = mercado ya descuenta casi todo = necesita más evidencia.
# ─────────────────────────────────────────────────────────────────────────────

EFICIENCIA_LIGA = {
    # Muy alta eficiencia: 6/8 criterios mínimos
    "Premier League":          "muy_alta",
    "Bundesliga":              "muy_alta",
    # Alta: 5/8 criterios
    "La Liga":                 "alta",
    "LaLiga":                  "alta",
    "Serie A":                 "alta",
    "Serie A Italia":          "alta",
    "Ligue 1":                 "alta",
    "Eredivisie":              "alta",
    # Media-alta: 4/8 criterios
    "Championship":            "media",
    "Serie B Italia":          "media",
    "Segunda España":          "media",
    "Bundesliga 2":            "media",
    "Ligue 2":                 "media",
    "Bélgica Pro League":      "media",
    "Primeira Liga":           "media",
    "Süper Lig":               "media",
    "Super Lig":               "media",
    # Media-baja: 3/8 criterios (más edge natural)
    "Eliteserien":             "baja",
    "Allsvenskan":             "baja",
    # Mundial: alta oportunidad por factores no preciados (calor, altitud)
    "FIFA World Cup 2026":     "media",
    "FIFA World Cup":          "media",
    "World Cup":               "media",
}


def _escape_md(texto: str) -> str:
    """Escapa caracteres especiales de Markdown v1 para evitar BadRequest de Telegram."""
    if not texto:
        return ""
    # Caracteres que rompen Markdown v1 en Telegram si no se escapan
    for ch in ['_', '*', '[', ']', '(', ')', '~', '`', '>', '#', '+',
               '-', '=', '|', '{', '}', '.', '!']:
        texto = texto.replace(ch, '\\' + ch)
    return texto

def _safe_send_md(texto: str) -> str:
    """Limpia texto para envío seguro en Telegram Markdown.
    Corrige marcadores de formato impares que causan BadRequest.
    """
    if not texto:
        return ""
    lineas = texto.split("\n")
    lineas_limpias = []
    for linea in lineas:
        # Si hay número impar de * o _ en la línea, eliminarlos todos
        # para evitar que Telegram falle el parse
        if linea.count("*") % 2 != 0:
            linea = linea.replace("*", "")
        if linea.count("_") % 2 != 0:
            linea = linea.replace("_", "")
        # Eliminar backticks sueltos
        if linea.count("`") % 2 != 0:
            linea = linea.replace("`", "'")
        lineas_limpias.append(linea)
    return "\n".join(lineas_limpias)


def get_umbral_confluencia(liga: str) -> int:
    """
    Retorna el número mínimo de criterios independientes necesarios
    para que un pick sea válido en esa liga.
    """
    nivel = EFICIENCIA_LIGA.get(liga, "alta")
    return {"muy_alta": 6, "alta": 5, "media": 4, "baja": 3}.get(nivel, 5)

def get_ajuste_score_eficiencia(liga: str) -> float:
    """
    Ajuste al score según eficiencia del mercado.
    Liga muy eficiente = penalización adicional (el mercado ya lo tiene).
    Liga poco eficiente = bonus (más edge disponible).
    """
    nivel = EFICIENCIA_LIGA.get(liga, "alta")
    return {"muy_alta": -0.3, "alta": 0.0, "media": +0.2, "baja": +0.4}.get(nivel, 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 3 — VETOS DE PICKS ESTRUCTURALMENTE DÉBILES
# Investigación: estos mercados tienen EV negativo demostrado en literatura.
# ─────────────────────────────────────────────────────────────────────────────

# Ligas top donde la victoria visitante directa tiene EV negativo (Wilkens 2026)
LIGAS_VETO_VICTORIA_VISITANTE = {
    "Premier League", "Bundesliga", "La Liga", "LaLiga",
    "Serie A", "Serie A Italia", "Ligue 1", "Eredivisie",
    "FIFA World Cup 2026", "FIFA World Cup", "World Cup",
}

def veto_victoria_visitante(jugada: str, liga: str) -> bool:
    """
    Retorna True (vetar) si el pick es victoria visitante directa en liga top.
    Wilkens 2026: 'backing away wins is consistently loss-making' en 11 temporadas.
    """
    if not jugada:
        return False
    j = jugada.lower()
    es_victoria_visitante = (
        j in ("victoria visitante", "away win", "2", "visitante gana")
        or "victoria visitante" in j
        or "away win" in j
    )
    return es_victoria_visitante and liga in LIGAS_VETO_VICTORIA_VISITANTE

def veto_dc_cuota_baja(cuota_dc: Optional[float]) -> bool:
    """
    Z7: DC solo cuando cuota ≥ 1.25. Si < 1.25, el mercado ya incorporó
    el empate y no hay valor marginal real en la protección del DC.
    """
    if cuota_dc is None:
        return False
    return float(cuota_dc) < 1.25

def veto_dc_prob_empate_baja(prob_empate: Optional[float]) -> bool:
    """
    Z7b: DC no tiene sentido si prob de empate < 18%.
    El tercer outcome protegido es tan improbable que el DC ofrece
    prácticamente el mismo valor que el 1X2 directo pero con cuota reducida.
    """
    if prob_empate is None:
        return False
    return float(prob_empate) < 0.18

def veto_over35_liga(liga: str) -> bool:
    """
    Z27: Over 3.5 solo en Bundesliga, Eredivisie, EPL (sin presión de posición)
    y mismatches del Mundial. En La Liga y Serie A: evitar salvo criterios extremos.
    """
    ligas_permitidas_over35 = {
        "Bundesliga", "Eredivisie", "Premier League",
        "FIFA World Cup 2026", "FIFA World Cup", "World Cup",
    }
    return liga not in ligas_permitidas_over35


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 4 — EFICIENCIA OFENSIVA Y xPTS (Regresión a la media)
# X1-X4, Y4-Y5: identificar equipos que sobre/infra-rinden respecto a su xG.
# ─────────────────────────────────────────────────────────────────────────────

def calcular_eficiencia_ofensiva(goles_reales: float, xg_estimado: float) -> float:
    """
    Ratio eficiencia = goles_reales / xG_estimado (últimos 6 partidos).
    > 1.30 = overperformer → pick penalizado (regresión esperada)
    < 0.70 = underperformer → pick bonificado (rebote estadístico inminente)
    1.0 = rendimiento esperado
    """
    if not xg_estimado or xg_estimado <= 0:
        return 1.0
    return round(goles_reales / xg_estimado, 3)

def ajuste_score_eficiencia_ofensiva(eficiencia_home: float, eficiencia_away: float,
                                      jugada: str) -> float:
    """
    Ajusta el score según la eficiencia ofensiva de los equipos.
    Para picks de goles (Over/Under), penaliza overperformers y bonifica underperformers.

    X3: eficiencia > 1.30 → overperformer → regresión pendiente → penalizar -0.2
    X4: eficiencia < 0.70 → underperformer → rebote estadístico → bonificar +0.2
    """
    ajuste = 0.0
    j = (jugada or "").lower()
    es_goles = any(x in j for x in ["over", "under", "goles", "1.5", "2.5", "3.5"])

    if not es_goles:
        return 0.0

    # Equipo local
    if eficiencia_home > 1.30:
        ajuste -= 0.2   # X3: overperformer local → goles futuros menores al xG
    elif eficiencia_home < 0.70:
        ajuste += 0.2   # X4: underperformer local → rebote estadístico

    # Equipo visitante
    if eficiencia_away > 1.30:
        ajuste -= 0.2
    elif eficiencia_away < 0.70:
        ajuste += 0.2

    return round(ajuste, 2)

def calcular_xpts_gap(xg_home_series: list, xg_away_series: list,
                       resultados: list) -> float:
    """
    Calcula la brecha xPTS - Puntos reales en los últimos N partidos.
    xPTS = (prob_victoria × 3) + (prob_empate × 1)
    donde prob se deriva del xG de cada partido via Poisson simple.

    Retorna gap positivo = equipo underperforming (el mercado lo castiga injustamente)
    Retorna gap negativo = equipo overperforming (el mercado lo sobrevalora)

    X1: gap ≥ +3.0 → bonus score +0.2
    X2: gap ≤ -3.0 → penalizar score -0.2
    """
    if not xg_home_series or not xg_away_series or not resultados:
        return 0.0

    import math

    def poisson_prob(k, lam):
        try:
            return math.exp(-lam) * (lam ** k) / math.factorial(k)
        except Exception:
            return 0.0

    xpts_total = 0.0
    pts_reales = 0.0

    for i, resultado in enumerate(resultados):
        if i >= len(xg_home_series) or i >= len(xg_away_series):
            break
        lam_h = max(0.2, xg_home_series[i])
        lam_a = max(0.2, xg_away_series[i])

        # Probabilidades via Poisson truncado a 5 goles
        p_home_win = 0.0
        p_draw = 0.0
        p_away_win = 0.0
        for gh in range(6):
            for ga in range(6):
                p = poisson_prob(gh, lam_h) * poisson_prob(ga, lam_a)
                if gh > ga:
                    p_home_win += p
                elif gh == ga:
                    p_draw += p
                else:
                    p_away_win += p

        xpts_total += p_home_win * 3 + p_draw * 1

        # Puntos reales: "W"=3, "D"=1, "L"=0
        r = str(resultado).upper()
        if r in ("W", "WIN", "G", "VICTORIA"):
            pts_reales += 3
        elif r in ("D", "DRAW", "EMPATE", "E"):
            pts_reales += 1

    return round(xpts_total - pts_reales, 2)

def ajuste_score_xpts_gap(xpts_gap: float) -> float:
    """
    X1: gap ≥ +3.0 → underperforming → el mercado lo castiga más de lo justo → +0.2
    X2: gap ≤ -3.0 → overperforming → el mercado lo sobrevalora → -0.2
    """
    if xpts_gap >= 3.0:
        return +0.2
    elif xpts_gap <= -3.0:
        return -0.2
    return 0.0


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 5 — TABLA AH COMPLETA: diff xG → línea correcta
# Z11-Z15, P13: el bot debe apostar la línea AH correcta según diferencia xG.
# ─────────────────────────────────────────────────────────────────────────────

def recomendar_linea_ah(xg_home: float, xg_away: float,
                         eficiencia_home: float = 1.0) -> dict:
    """
    Z11: Tabla completa diff xG → línea AH recomendada.
    Basada en cómo los bookmakers construyen la línea AH desde diferencia de goles.

    Retorna dict con: linea, descripcion, ajuste_eficiencia
    """
    diff = xg_home - xg_away  # positivo = local favorito

    # Ajuste por eficiencia: equipo que gana con bajo xG → línea más conservadora
    if eficiencia_home > 1.20:
        # Gana más de lo que su xG justifica → línea un escalón más conservadora
        diff = diff * 0.85

    if abs(diff) < 0.15:
        return {"linea": "AH(0)", "descripcion": "Partido muy equilibrado — DNB",
                "cuota_esperada": "1.85-1.95", "diff_xg": round(diff, 2)}
    elif diff > 0:
        # Local favorito
        if diff < 0.3:
            return {"linea": "AH(0)", "descripcion": "Favorito leve — DNB protege empate",
                    "cuota_esperada": "1.85-1.95", "diff_xg": round(diff, 2)}
        elif diff < 0.6:
            return {"linea": "AH(-0.25)", "descripcion": "Favorito leve-claro",
                    "cuota_esperada": "1.80-1.90", "diff_xg": round(diff, 2)}
        elif diff < 1.0:
            return {"linea": "AH(-0.5)", "descripcion": "Favorito claro — gana si gana",
                    "cuota_esperada": "1.75-1.85", "diff_xg": round(diff, 2)}
        elif diff < 1.5:
            return {"linea": "AH(-0.75)", "descripcion": "Favorito sólido — necesita margen",
                    "cuota_esperada": "1.75-1.85", "diff_xg": round(diff, 2)}
        elif diff < 2.0:
            return {"linea": "AH(-1.0)", "descripcion": "Gran favorito — margen esperado 1 gol",
                    "cuota_esperada": "1.70-1.80", "diff_xg": round(diff, 2)}
        elif diff < 2.5:
            return {"linea": "AH(-1.25)", "descripcion": "Mismatch claro",
                    "cuota_esperada": "1.75-1.85", "diff_xg": round(diff, 2)}
        else:
            return {"linea": "AH(-1.5)+", "descripcion": "Mismatch extremo",
                    "cuota_esperada": "Variable", "diff_xg": round(diff, 2)}
    else:
        # Visitante favorito (diff negativa)
        diff_abs = abs(diff)
        if diff_abs < 0.3:
            return {"linea": "AH(0)", "descripcion": "Visitante leve favorito — DNB",
                    "cuota_esperada": "1.85-1.95", "diff_xg": round(diff, 2)}
        elif diff_abs < 0.6:
            return {"linea": "AH(+0.25)", "descripcion": "Visitante favorito leve",
                    "cuota_esperada": "1.80-1.90", "diff_xg": round(diff, 2)}
        elif diff_abs < 1.0:
            return {"linea": "AH(+0.5)", "descripcion": "Visitante favorito claro",
                    "cuota_esperada": "1.75-1.85", "diff_xg": round(diff, 2)}
        else:
            return {"linea": "AH(+0.75)+", "descripcion": "Visitante gran favorito",
                    "cuota_esperada": "1.75-1.85", "diff_xg": round(diff, 2)}

def validar_linea_ah_ofertada(linea_recomendada: str, linea_ofertada: str) -> dict:
    """
    Z13: Verifica si la línea ofertada coincide con la recomendada.
    Si hay discrepancia de más de 0.5, puede haber información nueva en el mercado.
    Retorna: {"ok": bool, "advertencia": str}
    """
    orden = ["AH(+0.75)+", "AH(+0.5)", "AH(+0.25)", "AH(0)", "AH(-0.25)",
             "AH(-0.5)", "AH(-0.75)", "AH(-1.0)", "AH(-1.25)", "AH(-1.5)+"]
    try:
        idx_rec = next(i for i, x in enumerate(orden) if x in linea_recomendada)
        idx_ofe = next(i for i, x in enumerate(orden) if x in linea_ofertada)
        diff = abs(idx_rec - idx_ofe)
        if diff >= 2:
            return {"ok": False,
                    "advertencia": f"⚠️ Línea ofertada ({linea_ofertada}) difiere "
                                   f"de la recomendada ({linea_recomendada}) en {diff} escalones. "
                                   "Puede haber información nueva. Verificar antes de apostar."}
    except StopIteration:
        pass
    return {"ok": True, "advertencia": ""}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 6 — CRITERIOS O/U 2.5 REFINADOS (Z1-Z6)
# ─────────────────────────────────────────────────────────────────────────────

def calcular_combined_pct_over25(over25_home_en_casa: float,
                                  over25_away_de_visita: float) -> float:
    """
    Z1: Combined percentage como criterio primario para Over 2.5.
    over25_home_en_casa: % partidos Over 2.5 del local jugando en casa esta temporada.
    over25_away_de_visita: % partidos Over 2.5 del visitante jugando de visita.
    Retorna el combined % promedio.
    ≥ 65% = señal Over 2.5 independiente del xG.
    """
    return round((over25_home_en_casa + over25_away_de_visita) / 2, 1)

def criterios_over25(
    combined_pct: float,
    failed_to_score_away: float,    # Z3: % partidos donde visitante NO marcó de visita
    first_half_goals_both: float,   # Z4: % partidos con gol en primera mitad AMBOS
    rolling3_avg_goles: float,      # Z5: avg goles últimos 3 partidos AMBOS equipos
    liga_avg_over25: float,         # Z6: promedio Over 2.5 de la liga esta temporada
    shots_concedidos_home: float,   # X9-X10: shots concedidos por partido
    shots_concedidos_away: float,
) -> dict:
    """
    Sistema de criterios refinados para Over/Under 2.5.
    Retorna: {"señal": "over"|"under"|"neutral", "score_bonus": float, "motivos": list}
    """
    señal_over = 0
    señal_under = 0
    motivos = []

    # Z1: Combined % ≥ 65% → señal Over independiente del xG
    if combined_pct >= 65:
        señal_over += 2
        motivos.append(f"✅ Combined% {combined_pct}% ≥ 65% — señal Over independiente")
    elif combined_pct <= 40:
        señal_under += 2
        motivos.append(f"✅ Combined% {combined_pct}% ≤ 40% — señal Under independiente")

    # Z3: Visitante "failed to score" ≥ 35% → Under fuerte
    if failed_to_score_away >= 35:
        señal_under += 2
        motivos.append(f"✅ Visitante no marca en {failed_to_score_away}% visitas — Under fuerte")

    # Z4: First half goals both ≥ 55% → confirmador Over
    if first_half_goals_both >= 55:
        señal_over += 1
        motivos.append(f"✅ Ambos marcan 1ª mitad en {first_half_goals_both}% — confirmador Over")

    # Z5: Rolling 3 partidos avg > 3.0 → Over alta confianza
    if rolling3_avg_goles > 3.0:
        señal_over += 2
        motivos.append(f"✅ Últimos 3 partidos: {rolling3_avg_goles} goles/partido — Over alta confianza")
    elif rolling3_avg_goles < 1.8:
        señal_under += 2
        motivos.append(f"✅ Últimos 3 partidos: {rolling3_avg_goles} goles/partido — Under señal")

    # Z6: Liga promedio Over < 45% → ajustar umbral Under
    if liga_avg_over25 < 45:
        señal_under += 1
        motivos.append(f"ℹ️ Liga promedio Over 2.5 solo {liga_avg_over25}% — Under tiene valor estructural")

    # X9-X10: Shots concedidos como proxy pressing
    avg_shots_conc = (shots_concedidos_home + shots_concedidos_away) / 2
    if avg_shots_conc < 4:
        señal_under += 1
        motivos.append(f"✅ Defensas compactas: {avg_shots_conc:.1f} shots concedidos/pto — Under")
    elif avg_shots_conc > 6:
        señal_over += 1
        motivos.append(f"✅ Defensas porosas: {avg_shots_conc:.1f} shots concedidos/pto — Over")

    score_bonus = 0.0
    if señal_over >= 3:
        señal = "over"
        score_bonus = min(1.5, señal_over * 0.3)
    elif señal_under >= 3:
        señal = "under"
        score_bonus = min(1.5, señal_under * 0.3)
    else:
        señal = "neutral"

    return {"señal": señal, "score_bonus": round(score_bonus, 2), "motivos": motivos,
            "señal_over": señal_over, "señal_under": señal_under}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 7 — CRITERIOS DC REFINADOS (Z7-Z10)
# ─────────────────────────────────────────────────────────────────────────────

def cuota_justa_dc(prob_1: float, prob_x: float) -> float:
    """
    Fórmula de cuota justa para DC (1X o X2).
    prob_1 y prob_x en decimal [0-1] ya sin margen.
    Retorna la cuota justa. Si cuota ofertada > justa × 1.03 → hay valor.
    """
    prob_dc = prob_1 + prob_x
    if prob_dc <= 0:
        return 99.0
    return round(1 / prob_dc, 3)

def validar_dc(cuota_dc_ofertada: float, prob_empate: float,
               liga: str, es_x2: bool = False,
               forma_visitante_sin_derrota_pct: float = 50.0,
               h2h_empates: int = 1, h2h_total: int = 5) -> dict:
    """
    Validación completa de picks DC con criterios Z7-Z10.
    Retorna: {"valido": bool, "razones": list, "score_bonus": float}
    """
    razones = []
    score_bonus = 0.0
    invalido = False

    # Z7: Veto si cuota < 1.25
    if cuota_dc_ofertada < 1.25:
        razones.append(f"❌ Cuota DC {cuota_dc_ofertada} < 1.25 — sin valor marginal")
        invalido = True

    # Z7b: Veto si prob empate < 18%
    if prob_empate < 0.18:
        razones.append(f"❌ Prob empate {prob_empate:.1%} < 18% — protección DC ilusoria")
        invalido = True

    # Z8: X2 visitante — verificar forma reciente
    if es_x2 and forma_visitante_sin_derrota_pct < 30:
        razones.append(f"❌ Visitante pierde {100-forma_visitante_sin_derrota_pct:.0f}% de visitas — X2 sin valor real")
        invalido = True

    # Z9: 12 tiene valor cuando H2H tiene CERO empates
    if h2h_total >= 4 and h2h_empates == 0:
        razones.append(f"✅ H2H últimos {h2h_total} sin empates — 12 tiene valor")
        score_bonus += 0.3

    # Z10: La Liga DC 1X del local = el pick DC más confiable (76% victorias locales)
    if liga in ("La Liga", "LaLiga") and not es_x2:
        razones.append(f"✅ La Liga DC 1X — 76% victorias locales históricas, pick estructuralmente sólido")
        score_bonus += 0.4

    if invalido:
        return {"valido": False, "razones": razones, "score_bonus": 0.0}

    return {"valido": True, "razones": razones, "score_bonus": round(score_bonus, 2)}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 8 — CRITERIOS CORNERS REFINADOS (Z16-Z20)
# ─────────────────────────────────────────────────────────────────────────────

# Promedio de corners por liga (actualizado 2025-26)
CORNERS_PROM_LIGA = {
    "Premier League":   10.68,
    "Championship":     10.24,
    "Scottish Premier": 11.25,
    "Bundesliga":       10.12,
    "Bundesliga 2":      9.88,
    "Serie A Italia":    9.45,
    "La Liga":           9.20,
    "LaLiga":            9.20,
    "Ligue 1":           9.55,
    "Eredivisie":       10.30,
    "Bélgica Pro League": 9.80,
    "Süper Lig":         9.60,
    "FIFA World Cup 2026": 9.50,
    "FIFA World Cup":    9.50,
    "World Cup":         9.50,
}

# Selecciones con estilo de juego que genera corners (presión + bandas)
SELECCIONES_CORNERS_ALTO = {
    "Germany", "Netherlands", "France", "Belgium",
    "England", "Portugal", "Alemania", "Francia",
    "Países Bajos", "Holanda", "Bélgica", "Portugal",
}

def calcular_corners_v15(
    home_corners_prom: float,      # Corners promedio del local (últimos 6 partidos)
    away_corners_prom: float,      # Corners promedio del visitante
    home_corners_contra: float,    # Corners concedidos por el local (últimos 6)
    away_corners_contra: float,    # Corners concedidos por el visitante
    liga: str = "",
    home_name: str = "",
    away_name: str = "",
    es_mundial: bool = False,
) -> dict:
    """
    Sistema de criterios refinados para corners (Z16-Z20).
    Retorna señal de corners con score y motivos.

    Mejoras clave vs V14.3:
    - Verifica que AMBOS equipos contribuyen (no solo suma total)
    - Usa promedios de 6 partidos (más relevantes que 10)
    - Aplica promedio de liga como baseline
    - Considera matchup táctico (pressing vs técnico central)
    """
    motivos = []
    score_corners = 0.0
    señal = "neutral"
    linea_recomendada = None

    # Suma total esperada
    total_esperado = home_corners_prom + away_corners_prom
    # Corners concedidos vs rival — combinación ideal (Z17)
    combinacion_ideal = (home_corners_prom >= 5.5 and away_corners_contra >= 5.0) or \
                        (away_corners_prom >= 5.5 and home_corners_contra >= 5.0)

    # Ratio de contribución: evitar partidos donde uno domina 8-1
    if home_corners_prom > 0 and away_corners_prom > 0:
        ratio = max(home_corners_prom, away_corners_prom) / min(home_corners_prom, away_corners_prom)
    else:
        ratio = 10  # inválido

    contribucion_equitativa = ratio <= 2.5  # ambos contribuyen de forma balanceada

    # Z16: Ambos ≥ 5.0 → Over 9.5 probable
    if home_corners_prom >= 5.0 and away_corners_prom >= 5.0:
        score_corners += 2.0
        señal = "over"
        linea_recomendada = "Over 9.5"
        motivos.append(f"✅ Z16: Ambos ≥ 5 corners/pto — Over 9.5 probable (total: {total_esperado:.1f})")

    # Z17: Combinación ideal (atacante alto + defensa que concede muchos)
    if combinacion_ideal:
        score_corners += 1.5
        motivos.append("✅ Z17: Combinación ideal — corners_for alto vs corners_against alto del rival")

    # Verificar contribución equitativa (corrección crítica del modelo actual)
    if not contribucion_equitativa:
        score_corners -= 1.0
        motivos.append(f"⚠️ Dominio de corners muy asimétrico (ratio {ratio:.1f}x) — total menos predecible")

    # Z18: Mismatch → Over 8.5 aun cuando parece contratuintivo
    if total_esperado >= 8.5 and not contribucion_equitativa:
        señal = "over"
        linea_recomendada = "Over 8.5"
        motivos.append("ℹ️ Z18: Mismatch — favorito genera 5-6, rival bajo presión 3-4 — Over 8.5 válido")

    # Z19: Liga con promedio alto — Over 9.5 tiene EV positivo estructural
    prom_liga = CORNERS_PROM_LIGA.get(liga, 9.5)
    if prom_liga >= 10.0:
        score_corners += 0.5
        motivos.append(f"✅ Z19: {liga} promedia {prom_liga} corners/pto — Over 9.5 tiene EV estructural")

    # Z20: Matchup táctico para el Mundial
    if es_mundial:
        home_presion = home_name in SELECCIONES_CORNERS_ALTO
        away_presion = away_name in SELECCIONES_CORNERS_ALTO
        if home_presion or away_presion:
            score_corners += 0.5
            motivos.append("✅ Z20: Selección de pressing por bandas — genera corners adicionales")
        else:
            motivos.append("ℹ️ Z20: Ambas selecciones técnico-centrales — corners moderados")

    # Determinar señal final y línea
    if score_corners >= 3.0 and señal == "neutral":
        señal = "over"
        linea_recomendada = "Over 9.5" if total_esperado >= 9.5 else "Over 8.5"
    elif total_esperado < 7.5:
        señal = "under"
        linea_recomendada = "Under 8.5"
        motivos.append(f"ℹ️ Total esperado {total_esperado:.1f} — Under 8.5")

    # Score final clampado
    score_final = round(max(0.0, min(10.0, 5.0 + score_corners)), 1)

    return {
        "señal": señal,
        "linea_recomendada": linea_recomendada,
        "total_corners_esperado": round(total_esperado, 1),
        "contribucion_equitativa": contribucion_equitativa,
        "score": score_final,
        "motivos": motivos,
    }


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 9 — CRITERIOS OVER 1.5 MEJORADOS (Z21-Z25)
# ─────────────────────────────────────────────────────────────────────────────

def evaluar_over15_vs_over25(
    xg_combinado: float,
    cuota_over15: float,
    cuota_over25: float,
    scoring_rate_home: float,    # % partidos Over 1.5 del local en casa
    scoring_rate_away: float,    # % partidos Over 1.5 del visitante de visita
    liga: str = "",
    rebote_emocional: bool = False,  # Z25: equipo perdió último partido en casa
) -> dict:
    """
    Z21-Z25: Determina si Over 1.5 es mejor apuesta que Over 2.5 en el contexto dado.
    Retorna: {"mercado": "Over 1.5"|"Over 2.5"|"ambos", "score_bonus": float, "motivos": list}
    """
    motivos = []
    score_bonus = 0.0
    recomendar_over15 = False

    combined_pct = (scoring_rate_home + scoring_rate_away) / 2

    # Z22: Scoring rate ≥ 75% en roles → Over 1.5 sin necesitar xG alto
    if combined_pct >= 75:
        recomendar_over15 = True
        score_bonus += 0.5
        motivos.append(f"✅ Z22: Combined% {combined_pct:.0f}% ≥ 75% — Over 1.5 confiable")

    # Z21: xG zona gris (2.0-2.8) + cuota Over 1.5 ≥ 1.40 → Over 1.5 > Over 2.5
    if 2.0 <= xg_combinado <= 2.8 and cuota_over15 >= 1.40:
        recomendar_over15 = True
        score_bonus += 0.3
        motivos.append(f"✅ Z21: xG zona gris {xg_combinado} + cuota Over 1.5 {cuota_over15} — Over 1.5 captura el valor")

    # Z23: Goal expectancy ≥ 2.76 → selección ideal para Over 1.5
    if xg_combinado >= 2.76:
        score_bonus += 0.4
        motivos.append(f"✅ Z23: xG {xg_combinado} ≥ 2.76 — zona ideal para Over 1.5")

    # Z24: EPL 2025-26 promedia 2.77 → Over 1.5 ~80% hit rate estructural
    if liga in ("Premier League",) and xg_combinado >= 2.0:
        score_bonus += 0.3
        motivos.append("✅ Z24: EPL promedia 2.77 goles — Over 1.5 ~80% hit rate estructural esta temporada")

    # Z25: Rebote emocional → Over 1.5 más seguro
    if rebote_emocional:
        recomendar_over15 = True
        score_bonus += 0.2
        motivos.append("✅ Z25: Rebote emocional — equipo reacciona ofensivamente tras derrota en casa")

    # Cuándo Over 1.5 NO es mejor
    if cuota_over15 < 1.25:
        motivos.append(f"⚠️ Cuota Over 1.5 {cuota_over15} < 1.25 — EV demasiado bajo, considerar Over 2.5")
        recomendar_over15 = False
        score_bonus = 0.0

    mercado = "Over 1.5" if recomendar_over15 else ("Over 2.5" if xg_combinado >= 2.5 else "neutral")
    return {"mercado": mercado, "score_bonus": round(score_bonus, 2), "motivos": motivos}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 10 — CRITERIOS O/U 3.5 PROPIOS (Z26-Z29)
# ─────────────────────────────────────────────────────────────────────────────

def evaluar_over35(
    xg_combinado: float,
    xga_home: float,          # xG concedido por el local
    xga_away: float,          # xG concedido por el visitante
    h2h_avg_goles: float,     # Promedio de goles en H2H últimos 5
    liga: str = "",
    fase_mundial: str = "",   # "group", "R16", "QF", "SF", "F"
) -> dict:
    """
    Z26-Z29: Criterios propios separados para Over/Under 3.5.
    Retorna: {"señal": "over35"|"under35"|"neutral", "score": float, "motivos": list}
    """
    motivos = []
    score = 5.0
    señal = "neutral"

    # Z26: xG > 3.5 + AMBOS xGA > 1.5 → Over 3.5 EV real
    if xg_combinado > 3.5 and xga_home > 1.5 and xga_away > 1.5:
        score += 2.5
        señal = "over35"
        motivos.append(f"✅ Z26: xG {xg_combinado} + ambos xGA>{1.5} — Over 3.5 con EV real")
    elif xg_combinado > 3.5 and (xga_home <= 1.5 or xga_away <= 1.5):
        motivos.append("⚠️ Z26: xG alto pero solo UN equipo tiene xGA alto — riesgo de 3-0 sin llegar a 4")

    # Z27: Solo en ligas habilitadas
    if veto_over35_liga(liga):
        score -= 2.0
        señal = "neutral"
        motivos.append(f"❌ Z27: {liga} no habilitada para Over 3.5 — EV históricamente negativo")

    # Z28: H2H promedio ≥ 3.8 → Over 3.5 válido por historia
    if h2h_avg_goles >= 3.8:
        score += 1.5
        señal = "over35"
        motivos.append(f"✅ Z28: H2H promedio {h2h_avg_goles} ≥ 3.8 — Over 3.5 validado por historia")
    elif h2h_avg_goles < 3.2:
        score -= 0.5
        motivos.append(f"⚠️ H2H promedio {h2h_avg_goles} < 3.2 — mercado puede sobreestimar Over 3.5")

    # Z29: Under 3.5 en fases eliminatorias del Mundial (ROI +18.7% desde 1998)
    fases_tardias = {"QF", "SF", "F", "Final", "Semifinal", "Quarter"}
    if fase_mundial and any(f in fase_mundial for f in fases_tardias):
        score -= 2.0
        señal = "under35"
        motivos.append(f"✅ Z29: Fase eliminatoria tardía Mundial ({fase_mundial}) — Under 3.5 ROI +18.7% histórico")

    score_final = round(min(10.0, max(0.0, score)), 1)
    return {"señal": señal, "score": score_final, "motivos": motivos}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 11 — AJUSTES CALOR Y ALTITUD MUNDIAL 2026 (X5-X7, X14-X15)
# ─────────────────────────────────────────────────────────────────────────────

# Clasificación de sedes por riesgo de calor extremo
SEDES_CALOR_MUNDIAL = {
    # Calor extremo (>70% probabilidad WBGT >28°C)
    "Guadalajara":    {"calor": "extremo", "wbgt_prob": 0.882, "climatizado": False},
    "Miami":          {"calor": "extremo", "wbgt_prob": 0.880, "climatizado": False},
    "Kansas City":    {"calor": "alto",    "wbgt_prob": 0.650, "climatizado": False},
    "Philadelphia":   {"calor": "alto",    "wbgt_prob": 0.600, "climatizado": False},
    "New York":       {"calor": "moderado","wbgt_prob": 0.450, "climatizado": False},
    "Boston":         {"calor": "bajo",    "wbgt_prob": 0.250, "climatizado": False},
    "San Francisco":  {"calor": "bajo",    "wbgt_prob": 0.200, "climatizado": False},
    "Seattle":        {"calor": "bajo",    "wbgt_prob": 0.180, "climatizado": False},
    "Vancouver":      {"calor": "bajo",    "wbgt_prob": 0.150, "climatizado": False},
    # Climatizados (sin ajuste de calor)
    "Dallas":         {"calor": "ninguno", "wbgt_prob": 0.0,   "climatizado": True},
    "Houston":        {"calor": "ninguno", "wbgt_prob": 0.0,   "climatizado": True},
    "Atlanta":        {"calor": "ninguno", "wbgt_prob": 0.0,   "climatizado": True},
    "Los Angeles":    {"calor": "ninguno", "wbgt_prob": 0.0,   "climatizado": True},
    # México
    "Mexico City":    {"calor": "moderado","wbgt_prob": 0.350, "climatizado": False},
    # Canada
    "Toronto":        {"calor": "bajo",    "wbgt_prob": 0.200, "climatizado": False},
}

# Selecciones con mayor desventaja por calor (europeas del norte)
SELECCIONES_VULNERABLES_CALOR = {
    "France", "Francia", "Germany", "Alemania",
    "Netherlands", "Holanda", "Países Bajos",
    "Belgium", "Bélgica", "Scotland", "Escocia",
    "Czech Republic", "Chequia", "Denmark", "Dinamarca",
    "Sweden", "Suecia", "Norway", "Noruega",
    "Poland", "Polonia", "Uruguay",
}

def ajuste_xg_calor_mundial(
    sede: str,
    home_name: str,
    away_name: str,
    jornada_torneo: int = 1,  # 1, 2 o 3 en grupos; 4+ en eliminatorias
) -> dict:
    """
    X5-X7, X14-X15: Calcula el ajuste de xG esperado por condiciones de calor.
    Retorna: {"ajuste_xg": float, "ajuste_score": float, "motivos": list}
    """
    info_sede = SEDES_CALOR_MUNDIAL.get(sede, {"calor": "moderado", "wbgt_prob": 0.3, "climatizado": False})
    motivos = []
    ajuste_xg = 0.0
    ajuste_score = 0.0

    # X6: Sede climatizada → sin ajuste
    if info_sede["climatizado"]:
        motivos.append(f"ℹ️ X6: {sede} — estadio climatizado, sin ajuste por calor")
        return {"ajuste_xg": 0.0, "ajuste_score": 0.0, "motivos": motivos}

    # X5: Calor extremo (WBGT >28°C alta probabilidad) → -0.25 xG ambos
    if info_sede["calor"] == "extremo":
        ajuste_xg = -0.25
        ajuste_score = -0.3
        motivos.append(f"⚠️ X5: {sede} — calor extremo ({info_sede['wbgt_prob']:.0%} prob WBGT>28°C) → -0.25 xG")
    elif info_sede["calor"] == "alto":
        ajuste_xg = -0.12
        ajuste_score = -0.15
        motivos.append(f"⚠️ {sede} — calor alto → -0.12 xG")

    # X7: Equipos europeos del norte en sedes calurosas → penalización adicional
    home_vulnerable = home_name in SELECCIONES_VULNERABLES_CALOR
    away_vulnerable = away_name in SELECCIONES_VULNERABLES_CALOR

    if info_sede["calor"] in ("extremo", "alto"):
        if home_vulnerable:
            ajuste_score -= 0.10
            motivos.append(f"⚠️ X7: {home_name} — selección europea norte en calor extremo, ventaja reducida -0.10")
        if away_vulnerable:
            ajuste_score += 0.05  # favorece al local si el visitante es más afectado
            motivos.append(f"ℹ️ {away_name} — visitante vulnerable al calor, local beneficiado")

    # X15: Partidos tardíos del torneo → calor acumulado, penalización adicional
    if jornada_torneo >= 4 and info_sede["calor"] in ("extremo", "alto"):
        equipos_muy_expuestos = [t for t in [home_name, away_name] if t in SELECCIONES_VULNERABLES_CALOR]
        if equipos_muy_expuestos:
            ajuste_score -= 0.05
            motivos.append(f"⚠️ X15: Fase tardía + calor acumulado — {', '.join(equipos_muy_expuestos)} afectados")

    # X14: Guadalajara/Miami open-air → bonus Under 2.5
    if sede in ("Guadalajara", "Miami") and info_sede["calor"] == "extremo":
        motivos.append("✅ X14: Guadalajara/Miami — bonus Under 2.5 por reducción de ritmo por calor")

    return {
        "ajuste_xg": round(ajuste_xg, 3),
        "ajuste_score": round(ajuste_score, 3),
        "bonus_under25": sede in ("Guadalajara", "Miami") and info_sede["calor"] == "extremo",
        "motivos": motivos,
    }


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 12 — CLV TRACKING (N3)
# Sistema para registrar y calcular Closing Line Value en aprendizaje.json
# ─────────────────────────────────────────────────────────────────────────────

def registrar_cuota_apertura(picks_guardados: list, fixture_id: int,
                              jugada: str, cuota_apertura: float) -> None:
    """
    N3: Guarda la cuota de apertura en picks_guardados.json.
    Llamar cuando se genera el pick (lo antes posible).
    """
    for pick in picks_guardados:
        if (pick.get("fixture_id") == fixture_id and
                pick.get("jugada", "").lower() == jugada.lower()):
            pick["cuota_apertura"] = cuota_apertura
            pick["timestamp_apertura"] = datetime.utcnow().isoformat()
            break

def calcular_clv(cuota_pick: float, cuota_cierre: float) -> float:
    """
    N3: CLV = diferencia en probabilidad implícita entre cuota del pick y cuota de cierre.
    CLV positivo = apostamos mejor que el mercado de cierre → edge real.
    CLV negativo = el mercado se movió en nuestra contra → señal de falta de edge.

    Retorna CLV en puntos porcentuales de probabilidad implícita.
    """
    if not cuota_pick or not cuota_cierre or cuota_pick <= 1 or cuota_cierre <= 1:
        return 0.0
    # CLV positivo = apostamos a cuota MAYOR que la de cierre
    # (el mercado bajó la cuota = se volvió menos favorable = nosotros estábamos en precio mejor)
    # prob_cierre > prob_pick cuando cuota_cierre < cuota_pick → CLV positivo para el apostador
    prob_pick = 1 / cuota_pick
    prob_cierre = 1 / cuota_cierre
    return round((prob_cierre - prob_pick) * 100, 2)  # positivo = cuota bajó = apostamos mejor

def enriquecer_aprendizaje_clv(entrada_aprendizaje: dict,
                                cuota_cierre: float) -> dict:
    """
    N3: Enriquece un registro de aprendizaje.json con datos de CLV.
    Llamar en _registrar_aprendizaje() antes de guardar.
    """
    cuota_pick = entrada_aprendizaje.get("cuota")
    cuota_apertura = entrada_aprendizaje.get("cuota_apertura")

    if cuota_pick and cuota_cierre:
        clv = calcular_clv(float(cuota_pick), float(cuota_cierre))
        entrada_aprendizaje["clv"] = clv
        entrada_aprendizaje["cuota_cierre"] = cuota_cierre
        entrada_aprendizaje["clv_positivo"] = clv > 0

    if cuota_apertura and cuota_cierre:
        movimiento = round(((1/cuota_cierre) - (1/float(cuota_apertura))) * 100, 2)
        entrada_aprendizaje["movimiento_mercado"] = movimiento
        # Si el mercado se movió >8% en nuestra dirección → confirmación sharp
        entrada_aprendizaje["confirmacion_sharp"] = movimiento > 2.0

    return entrada_aprendizaje

def analizar_clv_historico(datos_aprendizaje: list) -> dict:
    """
    N3: Analiza el CLV histórico por mercado desde aprendizaje.json.
    Retorna estadísticas que permiten identificar dónde el bot tiene edge real.
    """
    por_mercado = {}
    for entrada in datos_aprendizaje:
        if "clv" not in entrada:
            continue
        mercado = entrada.get("mercado", "Desconocido")
        jugada = entrada.get("jugada", "")
        clave = f"{mercado}|{jugada}"
        if clave not in por_mercado:
            por_mercado[clave] = {"clv_sum": 0.0, "count": 0, "positivos": 0}
        por_mercado[clave]["clv_sum"] += entrada["clv"]
        por_mercado[clave]["count"] += 1
        if entrada["clv"] > 0:
            por_mercado[clave]["positivos"] += 1

    resultado = {}
    for clave, stats in por_mercado.items():
        n = stats["count"]
        if n < 5:
            continue
        resultado[clave] = {
            "clv_promedio": round(stats["clv_sum"] / n, 2),
            "pct_positivo": round(stats["positivos"] / n * 100, 1),
            "n_picks": n,
            "tiene_edge": stats["clv_sum"] / n > 0,
        }

    return resultado


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 13 — 3 NIVELES DE STAKE POR SCORE (P9)
# ─────────────────────────────────────────────────────────────────────────────

def calcular_stake_v15(score: float, prob: float, cuota: float,
                        bank: float, fraccion_kelly: float = 0.25) -> dict:
    """
    P9: 3 niveles de stake según score de confianza.
    Reemplaza el sistema binario actual (apuesta o no apuesta).

    Nivel 1 (score 7.0-8.4): 1 unidad — picks normales
    Nivel 2 (score 8.5-8.9): 2 unidades — alta confianza
    Nivel 3 (score 9.0+):    3 unidades — elite, máxima confianza

    Combinado con Kelly fraccionado para calcular importe real.
    """
    # Determinar nivel de stake
    if score >= 9.0:
        nivel = 3
        descripcion = "🔥 ELITE (3u)"
        fraccion = min(0.50, fraccion_kelly * 2)  # Kelly más agresivo en picks elite
    elif score >= 8.5:
        nivel = 2
        descripcion = "⭐ ALTA CONFIANZA (2u)"
        fraccion = fraccion_kelly
    elif score >= 7.0:
        nivel = 1
        descripcion = "📊 ESTÁNDAR (1u)"
        fraccion = fraccion_kelly * 0.5
    else:
        return {"nivel": 0, "stake": 0.0, "descripcion": "❌ Score insuficiente",
                "pct_bank": 0.0}

    # Kelly fraccionado
    prob_decimal = min(0.95, max(0.05, prob / 100))
    kelly_pct = (prob_decimal * cuota - 1) / (cuota - 1) if cuota > 1 else 0
    kelly_fraccionado = max(0, kelly_pct * fraccion)
    stake = round(bank * kelly_fraccionado, 2)

    # Límites de stake por nivel (protección de bank)
    max_pct_nivel = {1: 0.02, 2: 0.035, 3: 0.05}
    stake = min(stake, bank * max_pct_nivel[nivel])
    stake = max(0.0, stake)

    return {
        "nivel": nivel,
        "stake": stake,
        "descripcion": descripcion,
        "pct_bank": round(kelly_fraccionado * 100, 2),
        "kelly_bruto": round(kelly_pct * 100, 2),
    }


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 14 — EMPATE DIRECTO COMO MERCADO INDEPENDIENTE (P10, P15)
# ─────────────────────────────────────────────────────────────────────────────

def evaluar_empate_directo(
    prob_empate_modelo: float,    # % del modelo propio
    prob_empate_pinnacle: float,  # % implícita de Pinnacle (ya sin margen)
    cuota_empate: float,          # Cuota ofertada para el empate
    h2h_empates: int,
    h2h_total: int,
    liga: str = "",
) -> dict:
    """
    P10, P15: El empate como mercado independiente cuando hay valor real.
    Criterios: modelo > 28% + mercado < 30% + cuota ≥ 3.20.
    Retorna: {"recomendar": bool, "score": float, "motivos": list}
    """
    motivos = []
    score = 5.0
    recomendar = False

    # Criterio principal: modelo ve más empate que el mercado
    if prob_empate_modelo >= 28 and prob_empate_pinnacle < 30 and cuota_empate >= 3.20:
        recomendar = True
        score += 2.0
        edge_empate = prob_empate_modelo - prob_empate_pinnacle
        motivos.append(f"✅ Modelo {prob_empate_modelo:.0f}% > Pinnacle {prob_empate_pinnacle:.0f}% "
                       f"(edge {edge_empate:.0f}pp) + cuota {cuota_empate} — empate con valor")

    # Bonus por H2H con empates frecuentes
    if h2h_total >= 4:
        tasa_empates_h2h = h2h_empates / h2h_total
        if tasa_empates_h2h >= 0.40:
            score += 1.0
            motivos.append(f"✅ H2H {h2h_empates}/{h2h_total} empates ({tasa_empates_h2h:.0%}) — patrón de empates")

    # Ligas con alta tasa de empates (bonus estructural)
    if liga in ("Serie A", "Serie A Italia"):
        score += 0.5
        motivos.append("✅ Serie A — alta tasa de empates estructural (Juventus 16 empates 2024-25)")

    if not recomendar:
        motivos.append(f"❌ No hay edge en el empate: modelo {prob_empate_modelo:.0f}%, "
                       f"Pinnacle {prob_empate_pinnacle:.0f}%, cuota {cuota_empate}")

    return {
        "recomendar": recomendar,
        "score": round(min(10.0, score), 1),
        "motivos": motivos,
    }


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 15 — DETECCIÓN DE MOVIMIENTO DE CUOTAS SOSPECHOSO (X11-X12)
# ─────────────────────────────────────────────────────────────────────────────

def analizar_movimiento_cuota(
    cuota_hace_2h: float,
    cuota_actual: float,
    jugada: str,
    hay_noticias: bool = False,
) -> dict:
    """
    X11: Si cuota sube >8% sin noticias → posible lesión silenciosa o rotación.
    X12: Si cuota NO se mueve tras lesión conocida → ya estaba preciado.

    Retorna: {"flag": str, "accion": str, "pct_cambio": float}
    """
    if not cuota_hace_2h or not cuota_actual or cuota_hace_2h <= 1:
        return {"flag": "sin_datos", "accion": "continuar", "pct_cambio": 0.0}

    # Cambio en probabilidad implícita
    prob_antes = 1 / cuota_hace_2h
    prob_ahora = 1 / cuota_actual
    pct_cambio = round((prob_ahora - prob_antes) * 100, 2)  # positivo = cuota bajó (favorito)

    # X11: Cuota del favorito SUBIÓ >8% (prob bajó) sin noticias
    prob_cambio_abs = abs(pct_cambio)
    if pct_cambio < -8 and not hay_noticias:  # prob bajó = cuota subió
        return {
            "flag": "posible_lesion_silenciosa",
            "accion": "⚠️ Cuota subió >8% sin noticias — verificar lineup/lesiones antes de apostar",
            "pct_cambio": pct_cambio,
        }

    # X12: Freeze pattern — lesión conocida pero cuota no se movió
    if hay_noticias and prob_cambio_abs < 2:
        return {
            "flag": "ya_preciado",
            "accion": "ℹ️ Mercado no reaccionó a la noticia — información ya estaba incorporada",
            "pct_cambio": pct_cambio,
        }

    # Movimiento normal en favor del favorito → confirma pick
    if pct_cambio > 5:
        return {
            "flag": "dinero_sharp",
            "accion": "✅ Mercado se movió a favor — dinero sharp confirma el pick",
            "pct_cambio": pct_cambio,
        }

    return {"flag": "normal", "accion": "continuar", "pct_cambio": pct_cambio}



# ═════════════════════════════════════════════════════════════════════════════
# SECCIÓN 20F — V17: TODAS LAS VARIABLES INVESTIGADAS O/U 2.5
# ═════════════════════════════════════════════════════════════════════════════

# _math_v17 alias para Poisson
_math_v17 = __import__("math")

def calcular_gap_rating(shots_on_target: float, corners: float, partidos: int = 1) -> float:
    """GAP Rating (Wheatcroft 2020) — 0.8% ROI en 68,672 apuestas 12 años."""
    if partidos <= 0: return 0.0
    return round((shots_on_target * 1.5 + corners * 0.3) / partidos, 3)

def evaluar_gap_ou25(gap_home: float, gap_away: float,
                     gap_conc_home: float, gap_conc_away: float) -> dict:
    """Evalúa Over/Under 2.5 con GAP ratings."""
    gap_of = gap_home + gap_away
    gap_def = gap_conc_home + gap_conc_away
    diff = gap_of - gap_def
    if diff > 1.5:   return {"señal":"over",      "ajuste":0.5, "motivos":[f"GAP diff {diff:.2f}>1.5 → Over"], "gap_total":round(gap_of,2)}
    if diff > 0.8:   return {"señal":"over_mod",  "ajuste":0.3, "motivos":[f"GAP diff {diff:.2f} → Over moderado"], "gap_total":round(gap_of,2)}
    if diff < -1.5:  return {"señal":"under",     "ajuste":0.5, "motivos":[f"GAP diff {diff:.2f}<-1.5 → Under"], "gap_total":round(gap_of,2)}
    if diff < -0.8:  return {"señal":"under_mod", "ajuste":0.3, "motivos":[f"GAP diff {diff:.2f} → Under moderado"], "gap_total":round(gap_of,2)}
    return {"señal":"neutro","ajuste":0.0,"motivos":[],"gap_total":round(gap_of,2)}

def calcular_prob_over25_poisson_mejorado(shots_h: float, shots_a: float,
                                           ib_h: float, ib_a: float,
                                           sot_h: float, sot_a: float,
                                           xg_h: float=0.0, xg_a: float=0.0) -> dict:
    """Poisson mejorado con shots insidebox para mayor precisión en O/U 2.5."""
    def lam(sh, ib, sot):
        sh = max(sh, 0.1); ib = min(ib, sh); ob = max(sh-ib, 0)
        xg = ib*0.15 + ob*0.04
        if sh > 0: xg *= (0.7 + min(sot/sh,1.0)*0.6)
        return round(max(xg, 0.1), 3)
    lh = lam(shots_h, ib_h, sot_h)
    la = lam(shots_a, ib_a, sot_a)
    if xg_h > 0 and xg_a > 0:
        lh = round(lh*0.60 + xg_h*0.40, 3)
        la = round(la*0.60 + xg_a*0.40, 3)
    lt = lh + la
    try:
        p_under = sum(_math_v17.exp(-lt)*lt**k/_math_v17.factorial(k) for k in range(3))
    except: p_under = 0.5
    return {"lambda_home":lh,"lambda_away":la,"lambda_total":round(lt,3),
            "prob_over25":round((1-p_under)*100,2),"prob_under25":round(p_under*100,2)}

def calcular_gsax_proxy(gk_saves: float, sot_rival: float,
                         goles_rec: float, n: int=5) -> dict:
    """GSAX proxy: portero overperforming → regresión → señal Over."""
    if n <= 0: return {"gsax":0.0,"señal":"neutro","motivo":""}
    psxg = sot_rival * 0.33
    gsax = round((psxg - goles_rec) / n, 3)
    if gsax > 1.0:  return {"gsax":gsax,"señal":"over",  "motivo":f"GSAX {gsax:.2f}/pto: portero overperforming → regresión → Over"}
    if gsax > 0.5:  return {"gsax":gsax,"señal":"over_leve","motivo":f"GSAX {gsax:.2f}/pto"}
    if gsax < -0.5: return {"gsax":gsax,"señal":"under","motivo":f"GSAX {gsax:.2f}/pto: portero underperforming → Under"}
    return {"gsax":gsax,"señal":"neutro","motivo":""}

def calcular_npxg_proxy(xg: float, goles: float, shots: float) -> float:
    """npxG: xG ajustado eliminando penales inflados."""
    if shots<=0 or xg<=0: return xg
    if goles>xg*1.3 and shots>0:
        pen_est = round((goles-xg)/0.79)
        return round(max(xg - pen_est*0.79, xg*0.7), 2)
    return xg

MATCH_TYPE_BIAS = {"top_vs_bottom":+0.40,"mid_mid_atak":+0.25,"relegation":-0.15,
                   "top_vs_top":-0.35,"dead_rubber":-0.25,"cup_final":-0.30,
                   "europa_2nd":+0.20,"standard":0.00}

def clasificar_match_type(pos_h: int, pos_a: int, n: int=20,
                           desc_h: str="", desc_a: str="",
                           es_copa: bool=False, liga: str="") -> dict:
    """Clasifica el partido por tipo para ajustar Over/Under bias."""
    top = max(1, int(n*0.30)); bot = int(n*0.75)
    def es_rel(d): return any(x in (d or "").lower() for x in ["relegation","descenso"])
    def es_tit(d): return any(x in (d or "").lower() for x in ["title","champion","promotion"])
    if es_copa: t="cup_final"
    elif es_rel(desc_h) and es_rel(desc_a): t="relegation"
    elif pos_h<=top and pos_a<=top: t="top_vs_top"
    elif (pos_h<=top and pos_a>=bot) or (pos_a<=top and pos_h>=bot): t="top_vs_bottom"
    elif es_rel(desc_h) or es_rel(desc_a): t="relegation"
    else: t="standard"
    adj=MATCH_TYPE_BIAS.get(t,0.0)
    return {"match_type":t,"ajuste_score":adj,"motivo":f"Match type: {t} → {adj:+.2f}"}

TACTICAL_DNA = {
    "bundesliga":     {"over25_base":65,"top_top_under":0.00,"late_goals":0.28,"mid_block":0.15},
    "premier league": {"over25_base":57,"top_top_under":0.10,"late_goals":0.22,"mid_block":0.20},
    "la liga":        {"over25_base":50,"top_top_under":0.15,"late_goals":0.18,"mid_block":0.40},
    "laliga":         {"over25_base":50,"top_top_under":0.15,"late_goals":0.18,"mid_block":0.40},
    "serie a":        {"over25_base":48,"top_top_under":0.18,"late_goals":0.20,"mid_block":0.45},
    "serie a italia": {"over25_base":48,"top_top_under":0.18,"late_goals":0.20,"mid_block":0.45},
    "ligue 1":        {"over25_base":52,"top_top_under":0.10,"late_goals":0.28,"mid_block":0.30},
    "eredivisie":     {"over25_base":60,"top_top_under":0.05,"late_goals":0.22,"mid_block":0.10},
    "2. bundesliga":  {"over25_base":58,"top_top_under":0.05,"late_goals":0.25,"mid_block":0.15},
    "championship":   {"over25_base":56,"top_top_under":0.08,"late_goals":0.22,"mid_block":0.25},
    "champions league":{"over25_base":56,"top_top_under":0.12,"late_goals":0.24,"mid_block":0.30},
    "europa league":  {"over25_base":54,"top_top_under":0.10,"late_goals":0.22,"mid_block":0.25},
    "fifa world cup": {"over25_base":45,"top_top_under":0.20,"late_goals":0.19,"mid_block":0.35},
    "world cup":      {"over25_base":45,"top_top_under":0.20,"late_goals":0.19,"mid_block":0.35},
}

EQUIPOS_MID_BLOCK = {
    "atletico de madrid","atletico madrid","atlético de madrid","atletico",
    "getafe","osasuna","inter milan","inter","lazio","athletic bilbao",
    "brentford","crystal palace","wolves","wolverhampton","burnley",
}

def get_tactical_dna(liga: str) -> dict:
    ll = liga.lower().strip()
    for k,v in TACTICAL_DNA.items():
        if k in ll or ll in k: return v
    return {"over25_base":52,"top_top_under":0.08,"late_goals":0.20,"mid_block":0.25}

def tiene_mid_block(equipo: str) -> bool:
    return equipo.lower().strip() in EQUIPOS_MID_BLOCK

def detectar_steam_move(cuota_ap: float, cuota_act: float, mins: float) -> dict:
    """Steam move detector — caída >10% en <120min = sharp money."""
    if not cuota_ap or cuota_ap<=0: return {"steam":False,"ajuste":0.0,"motivo":""}
    mov = (cuota_ap-cuota_act)/cuota_ap
    if mov>=0.10 and mins<=120: return {"steam":True,"tipo":"steam_sharp","ajuste":0.5,"motivo":f"Steam sharp: -{mov:.0%} en {mins:.0f}min"}
    if mov>=0.05 and mins<=360: return {"steam":True,"ajuste":0.3,"motivo":f"Movimiento {mov:.0%} confirmado"}
    if mov<-0.05:               return {"steam":False,"ajuste":-0.4,"motivo":f"Cuota sube {abs(mov):.0%} → sin confirmar"}
    return {"steam":False,"ajuste":0.0,"motivo":""}

def calcular_congestion_21dias(fechas: list) -> dict:
    """FC1/CON1: Congestión 21 días → Under 68% si ≥5 partidos."""
    from datetime import datetime as _dt, timedelta as _td
    try:
        hoy=_dt.utcnow(); h21=hoy-_td(days=21)
        n=sum(1 for f in (fechas or []) if isinstance(f,str) and h21<=_dt.strptime(f[:10],"%Y-%m-%d")<=hoy)
    except: n=0
    if n>=5: return {"congestion":"alta","n":n,"ajuste_under":0.5,"motivo":f"Congestión: {n} ptdos/21días → Under 68%"}
    if n>=4: return {"congestion":"moderada","n":n,"ajuste_under":0.3,"motivo":f"Congestión moderada: {n} ptdos"}
    return {"congestion":"normal","n":n,"ajuste_under":0.0,"motivo":""}

def ajuste_climatico_ou25(temp: float=20, lluvia: float=0, viento: float=0,
                           estilo_h: str="mixto", estilo_a: str="mixto") -> dict:
    """WC1-WC4: Ajuste climático para Over/Under 2.5."""
    adj=0.0; f=[]
    if lluvia>5:   adj-=0.25; f.append(f"Lluvia intensa {lluvia}mm → Under")
    elif lluvia>2: adj-=0.10; f.append(f"Lluvia moderada {lluvia}mm")
    if viento>30:  adj-=0.20; f.append(f"Viento fuerte {viento}km/h")
    elif viento>15:adj-=0.10; f.append(f"Viento moderado {viento}km/h")
    if temp>32:    adj-=0.20; f.append(f"Calor extremo {temp}°C")
    elif temp<2:   adj-=0.10; f.append(f"Frío extremo {temp}°C")
    return {"ajuste_over25":round(adj,2),"factores":f,"adverso":adj<-0.15}

def evaluar_nuevo_entrenador(n_ptdos: int, xg_antes: float,
                              xg_ahora: float, cuota: float=2.0) -> dict:
    """NM1/NM2: Manager bounce es regresión a la media (Erasmus 2025)."""
    if n_ptdos>5: return {"nuevo_manager":False,"valor_rival":False,"ajuste":0.0,"motivos":[]}
    motivos=[]; adj=0.0; valor_rival=False
    if cuota<1.60 and n_ptdos<=3:
        adj=-0.3; valor_rival=True
        motivos.append(f"Manager bounce sobrevaluado — cuota {cuota} inflada")
    if xg_antes>0 and xg_antes>=xg_ahora*0.85:
        motivos.append("Mejora = regresión a la media, no rebote real")
    return {"nuevo_manager":True,"valor_rival":valor_rival,"ajuste":adj,"motivos":motivos}

def calcular_xt_proxy(passes_acc: float, shots_ib: float, dangerous: float) -> float:
    """xTP1: xT proxy con campos de statistics API."""
    return round((passes_acc or 0)*0.003 + (shots_ib or 0)*0.15 + (dangerous or 0)*0.005, 3)

def calcular_clv_timing_score(horas: float, cuota: float, cuota_cierre: float=0.0) -> dict:
    """CLV2: Timing score — cuanto antes mayor valor potencial."""
    clv = round((cuota/cuota_cierre-1)*100,2) if cuota_cierre>0 and cuota>0 else None
    if horas>=6:  return {"timing":"early","bonus_score":0.15,"clv_real":clv,"motivo":f"{horas:.0f}h antes — línea ineficiente"}
    if horas>=2:  return {"timing":"mid",  "bonus_score":0.05,"clv_real":clv,"motivo":f"{horas:.0f}h antes — timing moderado"}
    return {"timing":"late","bonus_score":-0.10,"clv_real":clv,"motivo":f"{horas:.0f}h antes — mercado ajustado"}

def calcular_motivacion_diferencial(pts_h: int, pts_a: int, n_partidos: int,
                                     desc_h: str="", desc_a: str="",
                                     pos_h: int=10, pos_a: int=10) -> dict:
    """MOT1: Motivación diferencial → ajuste score."""
    def mot(pos, desc, pts, n):
        s=0; d=(desc or "").lower()
        if any(x in d for x in ["title","champion","promotion"]): s+=10
        elif pos<=6 and n>15: s+=7
        elif 8<=pos<=14: s+=3
        if any(x in d for x in ["relegation","descenso","playoff"]): s+=9
        elif pos>=17: s+=8
        return s
    mh=mot(pos_h,desc_h,pts_h,n_partidos)
    ma=mot(pos_a,desc_a,pts_a,n_partidos)
    diff=mh-ma
    if abs(diff)>=8: return {"mot_home":mh,"mot_away":ma,"diferencia":diff,"ajuste":0.3,"motivo":f"MOT1: diff {abs(diff)}pts de motivación"}
    if abs(diff)>=5: return {"mot_home":mh,"mot_away":ma,"diferencia":diff,"ajuste":0.15,"motivo":f"MOT1: diff motivación moderada"}
    return {"mot_home":mh,"mot_away":ma,"diferencia":diff,"ajuste":0.0,"motivo":""}

def calcular_xg_corners(corners_h: float, corners_a: float) -> dict:
    """CK1: xG corners = corners × 0.031 (tasa validada 2025)."""
    xg_h=round(corners_h*0.031,3); xg_a=round(corners_a*0.031,3)
    xg_t=round(xg_h+xg_a,3)
    señal="over_bonus" if xg_t>0.4 else ("under_minor" if xg_t<0.15 else "neutro")
    return {"xg_h":xg_h,"xg_a":xg_a,"xg_total":xg_t,"señal":señal,
            "motivo":f"CK1: xG corners {xg_t:.3f}"}

def calcular_combined_pct_roles(over25_h_casa: float, over25_a_visita: float) -> dict:
    """Combined % por roles (más preciso que combinado total)."""
    c=round((over25_h_casa+over25_a_visita)/2,1)
    if c>=70: return {"combined":c,"señal":"over_alta","ajuste":0.6,"motivo":f"Combined%rol {c:.0f}% ≥70% → Over alta confianza"}
    if c>=65: return {"combined":c,"señal":"over_mod", "ajuste":0.4,"motivo":f"Combined%rol {c:.0f}%"}
    if c>=60: return {"combined":c,"señal":"over_leve","ajuste":0.2,"motivo":f"Combined%rol {c:.0f}%"}
    if c<=40: return {"combined":c,"señal":"under_fuerte","ajuste":0.6,"motivo":f"Combined%rol {c:.0f}% ≤40% → Under fuerte"}
    if c<=48: return {"combined":c,"señal":"under_mod","ajuste":0.3,"motivo":f"Combined%rol {c:.0f}% → Under"}
    return {"combined":c,"señal":"neutro","ajuste":0.0,"motivo":""}

def evaluar_top_vs_top_under(pos_h: int, pos_a: int, liga: str, n: int=20) -> dict:
    """Top vs Top Under bias estructural por liga."""
    top=max(1,int(n*0.30)); dna=get_tactical_dna(liga); bias=dna.get("top_top_under",0.08)
    if pos_h<=top and pos_a<=top:
        return {"es_top_top":True,"ajuste_under":round(-bias*3.0,2),"motivo":f"Top{top}vsTop{top} en {liga}: Under bias {bias:.0%}"}
    return {"es_top_top":False,"ajuste_under":0.0,"motivo":""}

CUOTA_MIN_OU25={"over25":1.65,"under25":1.75,"over25_elite":1.80,"under25_elite":1.85}

def validar_cuota_min_ou25(cuota: float, mercado: str, nivel: str="standard") -> dict:
    """Cuota mínima para EV positivo en O/U 2.5."""
    k=f"{mercado.lower()}_elite" if nivel=="elite" else mercado.lower()
    minimo=CUOTA_MIN_OU25.get(k,CUOTA_MIN_OU25.get(mercado.lower(),1.65))
    return {"valido":cuota>=minimo,"minimo":minimo,"motivo":f"Cuota {cuota} {'≥' if cuota>=minimo else '<'} mínimo {minimo}"}

def calcular_h2h_over_rate(h2h: list) -> dict:
    """H2H Over rate — últimos 5 partidos."""
    if not h2h: return {"rate":50.0,"señal":"neutro","ajuste":0.0,"motivo":"Sin H2H"}
    v=h2h[:5]; over=sum(1 for p in v if (p.get("goals_home",0)+p.get("goals_away",0))>=3)
    rate=round(over/len(v)*100,1) if v else 50.0
    if rate>=80: return {"rate":rate,"señal":"over_fuerte","ajuste":0.5,"motivo":f"H2H {rate:.0f}% Over 2.5"}
    if rate>=60: return {"rate":rate,"señal":"over_mod",  "ajuste":0.2,"motivo":f"H2H {rate:.0f}% Over 2.5"}
    if rate<=20: return {"rate":rate,"señal":"under_fuerte","ajuste":0.5,"motivo":f"H2H {rate:.0f}% Over → Under"}
    if rate<=40: return {"rate":rate,"señal":"under_mod", "ajuste":0.2,"motivo":f"H2H {rate:.0f}% → Under leve"}
    return {"rate":rate,"señal":"neutro","ajuste":0.0,"motivo":""}


def evaluar_sistema_ou25_especializado(
    liga: str="", eq_home: str="", eq_away: str="",
    pos_home: int=10, pos_away: int=10,
    desc_home: str="", desc_away: str="",
    xg_home: float=0.0, xg_away: float=0.0,
    shots_h: float=0.0, shots_a: float=0.0,
    ib_h: float=0.0, ib_a: float=0.0,
    sot_h: float=0.0, sot_a: float=0.0,
    corners_h: float=0.0, corners_a: float=0.0,
    over25_h_casa: float=50.0, over25_a_visita: float=50.0,
    ht_rate_h: float=0.5, ht_rate_a: float=0.5,
    gk_saves_h: float=0.0, sot_rival_h: float=0.0, goles_rec_h: float=0.0,
    passes_acc_h: float=0.0, dangerous_h: float=0.0,
    passes_acc_a: float=0.0, dangerous_a: float=0.0,
    cuota_over25: float=0.0, cuota_under25: float=0.0,
    cuota_ap_over: float=0.0,
    fechas_h: list=None, fechas_a: list=None,
    h2h_list: list=None,
    temp: float=20.0, lluvia: float=0.0, viento: float=0.0,
    horas_antes: float=6.0,
    nm_h: int=99, nm_a: int=99,
    pts_h: int=0, pts_a: int=0, n_partidos: int=20,
) -> dict:
    """
    Sistema maestro especializado O/U 2.5.
    Evalúa todas las variables investigadas.
    Score ≥8.0 + cuota válida = pick recomendado.
    Para 5 picks/día de alta calidad: score ≥8.5.
    """
    so=5.0; su=5.0; sig_o=[]; sig_u=[]

    # GAP Rating
    g=evaluar_gap_ou25(calcular_gap_rating(sot_h,corners_h),
                       calcular_gap_rating(sot_a,corners_a),
                       calcular_gap_rating(sot_rival_h,corners_a),
                       calcular_gap_rating(sot_a,corners_h))
    if "over" in g["señal"]: so+=g["ajuste"]; sig_o+=g["motivos"][:1]
    elif "under" in g["señal"]: su+=g["ajuste"]; sig_u+=g["motivos"][:1]

    # Poisson mejorado
    p=calcular_prob_over25_poisson_mejorado(shots_h,shots_a,ib_h,ib_a,sot_h,sot_a,xg_home,xg_away)
    if p["prob_over25"]>=65: so+=(p["prob_over25"]-60)/20; sig_o.append(f"Poisson {p['prob_over25']:.0f}% Over")
    elif p["prob_under25"]>=65: su+=(p["prob_under25"]-60)/20; sig_u.append(f"Poisson {p['prob_under25']:.0f}% Under")

    # GSAX proxy
    if gk_saves_h>0:
        gs=calcular_gsax_proxy(gk_saves_h,sot_rival_h,goles_rec_h)
        if gs["señal"]=="over": so+=0.4; sig_o.append(gs["motivo"])
        elif gs["señal"]=="under": su+=0.3; sig_u.append(gs["motivo"])

    # Match type
    mt=clasificar_match_type(pos_home,pos_away,20,desc_home,desc_away,liga=liga)
    if mt["ajuste_score"]>0: so+=mt["ajuste_score"]; sig_o.append(mt["motivo"])
    elif mt["ajuste_score"]<0: su+=abs(mt["ajuste_score"]); sig_u.append(mt["motivo"])

    # Tactical DNA
    dna=get_tactical_dna(liga)
    if dna["over25_base"]>=62: so+=0.3; sig_o.append(f"Liga goleadora {dna['over25_base']}% Over")
    elif dna["over25_base"]<=48: su+=0.4; sig_u.append(f"Liga defensiva {dna['over25_base']}% Over")
    if tiene_mid_block(eq_home) or tiene_mid_block(eq_away):
        su+=0.4; sig_u.append("Mid-block style → Under bonus")

    # Combined % roles
    cr=calcular_combined_pct_roles(over25_h_casa,over25_a_visita)
    if "over" in cr["señal"]: so+=cr["ajuste"]; sig_o.append(cr["motivo"])
    elif "under" in cr["señal"]: su+=cr["ajuste"]; sig_u.append(cr["motivo"])

    # HT scoring rate
    ht=(ht_rate_h+ht_rate_a)/2
    if ht>=0.65: so+=0.35; sig_o.append(f"HT scoring {ht:.0%} → Over")
    elif ht<=0.35: su+=0.35; sig_u.append(f"HT scoring {ht:.0%} → Under")

    # xG corners CK1
    ck=calcular_xg_corners(corners_h,corners_a)
    if ck["señal"]=="over_bonus": so+=0.2; sig_o.append(ck["motivo"])

    # Top vs Top Under
    tvt=evaluar_top_vs_top_under(pos_home,pos_away,liga)
    if tvt["es_top_top"]: su+=abs(tvt["ajuste_under"]); sig_u.append(tvt["motivo"])

    # Congestión
    ch=calcular_congestion_21dias(fechas_h or [])
    ca=calcular_congestion_21dias(fechas_a or [])
    mc=max(ch["ajuste_under"],ca["ajuste_under"])
    if mc>0:
        su+=mc
        mot_c=ch["motivo"] if ch["ajuste_under"]>ca["ajuste_under"] else ca["motivo"]
        if mot_c: sig_u.append(mot_c)

    # Clima
    cl=ajuste_climatico_ou25(temp,lluvia,viento)
    if cl["ajuste_over25"]<-0.10: su+=abs(cl["ajuste_over25"])*0.8; sig_u+=cl["factores"][:1]

    # H2H
    h=calcular_h2h_over_rate(h2h_list or [])
    if "over" in h["señal"]: so+=h["ajuste"]; sig_o.append(h["motivo"])
    elif "under" in h["señal"]: su+=h["ajuste"]; sig_u.append(h["motivo"])

    # Steam move
    if cuota_ap_over>0 and cuota_over25>0:
        mins=max(1.0,(6.0-horas_antes)*60)
        st=detectar_steam_move(cuota_ap_over,cuota_over25,mins)
        so+=st["ajuste"]
        if st["motivo"]: sig_o.append(st["motivo"])

    # xT proxy
    xt=calcular_xt_proxy(passes_acc_h,ib_h,dangerous_h)+calcular_xt_proxy(passes_acc_a,ib_a,dangerous_a)
    if xt>0.8: so+=0.3; sig_o.append(f"xT proxy {xt:.2f} → alta amenaza")

    # Nuevo entrenador
    for np,xga,xgc,cuo in [(nm_h,xg_away,xg_home,cuota_over25),(nm_a,xg_home,xg_away,cuota_over25)]:
        if np<=5:
            nm=evaluar_nuevo_entrenador(np,xga,xgc,cuo)
            if nm["ajuste"]<0: so+=nm["ajuste"]; sig_o+=nm["motivos"][:1]

    # Motivación
    mo=calcular_motivacion_diferencial(pts_h,pts_a,n_partidos,desc_home,desc_away,pos_home,pos_away)
    if abs(mo["diferencia"])>5:
        so+=mo["ajuste"]*0.5
        if mo["motivo"]: sig_o.append(mo["motivo"])

    # Normalizar
    so=round(min(10.0,max(0.0,so)),1)
    su=round(min(10.0,max(0.0,su)),1)

    # Pick principal
    if so>=su:
        pick="over25"; score=so; sigs=sig_o[:5]; cuo=cuota_over25
    else:
        pick="under25"; score=su; sigs=sig_u[:5]; cuo=cuota_under25

    cuo_ok=validar_cuota_min_ou25(cuo or 1.5,pick,"elite" if score>=9.0 else "standard")
    nivel="ELITE" if score>=9.0 else ("ALTA" if score>=8.5 else ("MEDIA" if score>=8.0 else "BAJA"))
    clv=calcular_clv_timing_score(horas_antes, cuo or 1.5)

    return {
        "pick":pick,"score":score,"score_over":so,"score_under":su,
        "nivel":nivel,"señales":sigs,"cuota_valida":cuo_ok["valido"],
        "poisson":p,"gap_total":g.get("gap_total",0),
        "match_type":mt["match_type"],"clv_timing":clv["timing"],
        "recomendar":score>=8.0 and cuo_ok["valido"],
    }

# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 20E — V16: Funciones de acumulación y ratios nuevos
# ─────────────────────────────────────────────────────────────────────────────

def actualizar_historial_arbitro(arbitro: str, yellow_home: int, yellow_away: int,
                                  red_home: int, red_away: int, liga: str = "") -> None:
    """
    V9/V16: Acumula el historial de tarjetas por árbitro en REFEREE_FILE.
    Se llama en _registrar_aprendizaje() después de cada partido finalizado.
    Permite calcular el referee strictness score (tarjetas promedio/partido).
    """
    if not arbitro:
        return
    try:
        datos = leer_json(REFEREE_FILE) or {}
        if arbitro not in datos:
            datos[arbitro] = {"partidos": 0, "yellows_total": 0, "reds_total": 0,
                              "yellows_home": 0, "yellows_away": 0, "ligas": []}
        d = datos[arbitro]
        d["partidos"] += 1
        d["yellows_total"] += yellow_home + yellow_away
        d["reds_total"] += red_home + red_away
        d["yellows_home"] += yellow_home
        d["yellows_away"] += yellow_away
        if liga and liga not in d["ligas"]:
            d["ligas"].append(liga)
        guardar_json_lista(REFEREE_FILE, datos)
    except Exception as e:
        print(f"WARN arbitro historial: {e}")

def get_referee_strictness(arbitro: str) -> dict:
    """
    V9/V16: Retorna el perfil de estrictez del árbitro.
    - yellows_per_game > 4.5: árbitro estricto → Over tarjetas
    - yellows_per_game < 2.5: árbitro permisivo → Under tarjetas
    - away_bias: si amarillas_visitante >> amarillas_local → home bias fuerte
    """
    if not arbitro:
        return {"conocido": False, "yellows_per_game": 3.5, "away_bias": 0.0, "partidos": 0}
    try:
        datos = leer_json(REFEREE_FILE) or {}
        d = datos.get(arbitro)
        if not d or d.get("partidos", 0) < 5:
            return {"conocido": False, "yellows_per_game": 3.5, "away_bias": 0.0,
                    "partidos": d.get("partidos", 0) if d else 0}
        n = d["partidos"]
        ypm = round(d["yellows_total"] / n, 2)
        # Away bias: cuántas más amarillas recibe el visitante vs local por partido
        away_bias = round((d["yellows_away"] - d["yellows_home"]) / n, 2)
        return {
            "conocido": True,
            "yellows_per_game": ypm,
            "reds_per_game": round(d["reds_total"] / n, 3),
            "away_bias": away_bias,
            "partidos": n,
            "estricto": ypm > 4.5,
            "permisivo": ypm < 2.5,
            "home_bias_fuerte": away_bias > 0.8,  # visitante recibe +0.8 amarillas/pto
        }
    except Exception:
        return {"conocido": False, "yellows_per_game": 3.5, "away_bias": 0.0, "partidos": 0}


def calcular_ratios_v16(ctx: dict) -> dict:
    """
    V16: Calcula todos los ratios nuevos a partir de los campos extraídos de la API.
    Retorna un dict con los ratios listos para usar en los scores.
    """
    ratios = {}

    # ── xG por disparo (shot quality index) — V2 ─────────────────────────────
    for team in ("home", "away"):
        shots_ib = ctx.get(f"{team}_shots_insidebox", 0) or 0
        shots_total = ctx.get(f"{team}_shots_total", 1) or 1
        shots_oob = ctx.get(f"{team}_shots_outsidebox", 0) or 0
        blocked = ctx.get(f"{team}_blocked_shots", 0) or 0
        # xG mejorado: tiros dentro = 0.15 xG/tiro, fuera = 0.04, bloqueados = 0.02
        xg_mejorado = shots_ib * 0.15 + shots_oob * 0.04 + (shots_total - shots_ib - shots_oob) * 0.02
        ratios[f"{team}_xg_shot_quality"] = round(xg_mejorado, 2)
        # Índice de calidad: xG_mejorado / xG_base
        xg_base = ctx.get(f"{team}_xg_pred", 1.0) or 1.0
        ratios[f"{team}_shot_quality_idx"] = round(xg_mejorado / max(xg_base, 0.1), 2)

    # ── GOE (Goals Over Expected) — V4 ────────────────────────────────────────
    for team in ("home", "away"):
        goles = ctx.get(f"{team}_goles_favor_prom", 0) or 0
        xg = ctx.get(f"{team}_xg_pred", goles) or goles
        ratios[f"{team}_goe"] = round(float(goles) - float(xg), 2)

    # ── Field tilt — V6 ───────────────────────────────────────────────────────
    c_home = ctx.get("home_corners_prom", 0) or 0
    c_away = ctx.get("away_corners_prom", 0) or 0
    total_c = c_home + c_away
    ratios["home_field_tilt"] = round(c_home / max(total_c, 1), 3)
    ratios["away_field_tilt"] = round(c_away / max(total_c, 1), 3)

    # ── Possession efficiency — V18 ────────────────────────────────────────────
    for team in ("home", "away"):
        xg = ctx.get(f"{team}_xg_pred", 0) or 0
        pos = ctx.get(f"{team}_possession", 50) or 50
        ratios[f"{team}_possession_efficiency"] = round(float(xg) / max(float(pos), 1) * 100, 3)

    # ── PPDA proxy — V5 ────────────────────────────────────────────────────────
    for team in ("home", "away"):
        fouls = ctx.get(f"{team}_fouls", 0) or 0
        pos = ctx.get(f"{team}_possession", 50) or 50
        passes = ctx.get(f"{team}_passes_total", 1) or 1
        if fouls > 0:
            ratios[f"{team}_ppda_proxy"] = round(passes / max(fouls, 1), 2)
        else:
            ratios[f"{team}_ppda_proxy"] = 10.0  # sin datos = neutral

    # ── Home/Away split goles (de standings) — V16 ────────────────────────────
    for team in ("home", "away"):
        es_local = (team == "home")
        if es_local:
            gf_split = ctx.get("home_goles_favor_casa", 0) or 0
            gc_split = ctx.get("home_goles_contra_casa", 0) or 0
            played_split = ctx.get("home_played_casa", 1) or 1
        else:
            gf_split = ctx.get("away_goles_favor_visita", 0) or 0
            gc_split = ctx.get("away_goles_contra_visita", 0) or 0
            played_split = ctx.get("away_played_visita", 1) or 1
        if played_split > 0:
            ratios[f"{team}_gf_split"] = round(gf_split / played_split, 2)
            ratios[f"{team}_gc_split"] = round(gc_split / played_split, 2)
        else:
            ratios[f"{team}_gf_split"] = 0.0
            ratios[f"{team}_gc_split"] = 0.0

    # ── Opponent-adjusted goles (V16) ─────────────────────────────────────────
    # Normalizar por ranking del rival: rival top10 = factor 0.7, rival bottom10 = factor 1.3
    pos_home = ctx.get("home_posicion", 10) or 10
    pos_away = ctx.get("away_posicion", 10) or 10
    total_equipos = 20  # estándar liga top
    factor_rival_home = round(0.7 + (pos_away / total_equipos) * 0.6, 2)  # rival débil = factor alto
    factor_rival_away = round(0.7 + (pos_home / total_equipos) * 0.6, 2)
    ratios["home_gf_opp_adj"] = round(ratios.get("home_gf_split", 0) * factor_rival_home, 2)
    ratios["away_gf_opp_adj"] = round(ratios.get("away_gf_split", 0) * factor_rival_away, 2)

    # ── Scoring first proxy — V17 ─────────────────────────────────────────────
    for team in ("home", "away"):
        ht_rate = ctx.get(f"{team}_ht_scoring_rate", 0.5) or 0.5
        scoring_l5_str = ctx.get(f"{team}_scoring_rate_l5", "50%") or "50%"
        try:
            scoring_l5 = float(str(scoring_l5_str).replace("%", "")) / 100
        except Exception:
            scoring_l5 = 0.5
        # Prob de marcar primero ≈ promedio de: scoring rate HT + scoring rate L5
        ratios[f"{team}_scoring_first_prob"] = round((ht_rate + scoring_l5) / 2, 3)

    # ── API under_over como señal directa — Grupo 2 ───────────────────────────
    under_over = ctx.get("api_under_over", "")
    if under_over == "+2.5":
        ratios["api_over25_signal"] = 1      # API dice Over
    elif under_over == "-2.5":
        ratios["api_over25_signal"] = -1     # API dice Under
    else:
        ratios["api_over25_signal"] = 0      # sin señal

    # ── Comparison fields como scores relativos — Grupo 2 ─────────────────────
    def pct_to_float(s):
        try: return float(str(s or "50").replace("%", "")) / 100
        except: return 0.5

    ratios["cmp_att_edge"] = round(pct_to_float(ctx.get("api_cmp_att_home")) -
                                    pct_to_float(ctx.get("api_cmp_att_away")), 3)
    ratios["cmp_def_edge"] = round(pct_to_float(ctx.get("api_cmp_def_home")) -
                                    pct_to_float(ctx.get("api_cmp_def_away")), 3)
    ratios["cmp_form_edge"] = round(pct_to_float(ctx.get("api_cmp_form_home")) -
                                     pct_to_float(ctx.get("api_cmp_form_away")), 3)

    # ── VAR por liga (V10) — ajuste home advantage ─────────────────────────────
    LIGAS_CON_VAR = {
        "Premier League", "La Liga", "LaLiga", "Serie A", "Serie A Italia",
        "Bundesliga", "Ligue 1", "Eredivisie", "Champions League", "Europa League",
        "FIFA World Cup", "FIFA World Cup 2026", "World Cup",
    }
    liga_ctx = ctx.get("liga_nombre", "") or ""
    ratios["tiene_var"] = any(l.lower() in liga_ctx.lower() for l in LIGAS_CON_VAR)
    # Con VAR: home advantage reducido ~15% (menos bias de árbitro)
    ratios["home_advantage_factor"] = 0.85 if ratios["tiene_var"] else 1.0

    # ── Competition level xG adjustment (V27) ─────────────────────────────────
    # Mundial y eliminatorias: porteros mejores → xG de liga doméstica se convierte menos
    FACTOR_XG_COMPETICION = {
        "world cup": 0.85, "mundial": 0.85, "champions league": 0.90,
        "europa league": 0.92, "premier league": 1.0, "bundesliga": 1.0,
    }
    factor_xg = 1.0
    for comp, factor in FACTOR_XG_COMPETICION.items():
        if comp in liga_ctx.lower():
            factor_xg = factor
            break
    ratios["factor_xg_competicion"] = factor_xg

    return ratios


def ajuste_score_v16(score_base: float, ratios: dict, jugada: str,
                      arbitro_perfil: dict = None) -> dict:
    """
    V16: Aplica todos los ajustes de score basados en los nuevos ratios.
    Retorna: {"score_final": float, "ajustes": list}
    """
    ajuste = 0.0
    ajustes = []
    j = (jugada or "").lower()
    es_goles = any(x in j for x in ["over", "under", "goles", "1.5", "2.5", "3.5"])

    # ── API under_over signal ─────────────────────────────────────────────────
    api_signal = ratios.get("api_over25_signal", 0)
    if api_signal == 1 and "over 2.5" in j:
        ajuste += 0.4
        ajustes.append("API confirma Over 2.5: +0.40")
    elif api_signal == -1 and "under 2.5" in j:
        ajuste += 0.4
        ajustes.append("API confirma Under 2.5: +0.40")
    elif api_signal == 1 and "under 2.5" in j:
        ajuste -= 0.5
        ajustes.append("API contradice Under 2.5: -0.50")
    elif api_signal == -1 and "over 2.5" in j:
        ajuste -= 0.5
        ajustes.append("API contradice Over 2.5: -0.50")

    # ── Shot quality index ────────────────────────────────────────────────────
    if es_goles:
        sq_home = ratios.get("home_shot_quality_idx", 1.0)
        sq_away = ratios.get("away_shot_quality_idx", 1.0)
        avg_sq = (sq_home + sq_away) / 2
        if avg_sq > 1.3:
            ajuste += 0.3
            ajustes.append(f"Shot quality alta ({avg_sq:.2f}): +0.30")
        elif avg_sq < 0.7:
            ajuste -= 0.3
            ajustes.append(f"Shot quality baja ({avg_sq:.2f}): -0.30")

    # ── GOE (regresión a la media mejorada) ────────────────────────────────────
    goe_home = ratios.get("home_goe", 0.0)
    goe_away = ratios.get("away_goe", 0.0)
    if es_goles:
        goe_total = goe_home + goe_away
        if goe_total > 1.5:
            ajuste -= 0.2
            ajustes.append(f"GOE total alto ({goe_total:.1f}): regresión esperada -0.20")
        elif goe_total < -1.5:
            ajuste += 0.2
            ajustes.append(f"GOE total bajo ({goe_total:.1f}): rebote esperado +0.20")

    # ── Home/Away split ajuste (el más importante según investigación) ─────────
    if es_goles:
        gf_h_split = ratios.get("home_gf_split", 0)
        gf_a_split = ratios.get("away_gf_split", 0)
        total_split = gf_h_split + gf_a_split
        if total_split > 3.2 and "over" in j:
            ajuste += 0.4
            ajustes.append(f"Split home/away: {total_split:.1f} goles/pto → Over confirmado: +0.40")
        elif total_split < 1.5 and "under" in j:
            ajuste += 0.4
            ajustes.append(f"Split home/away: {total_split:.1f} goles/pto → Under confirmado: +0.40")

    # ── Opponent-adjusted goles ────────────────────────────────────────────────
    if es_goles:
        gf_adj_total = ratios.get("home_gf_opp_adj", 0) + ratios.get("away_gf_opp_adj", 0)
        if gf_adj_total > 3.5 and "over" in j:
            ajuste += 0.3
            ajustes.append(f"Opponent-adjusted: {gf_adj_total:.1f} → Over: +0.30")
        elif gf_adj_total < 1.8 and "under" in j:
            ajuste += 0.3
            ajustes.append(f"Opponent-adjusted: {gf_adj_total:.1f} → Under: +0.30")

    # ── Comparison fields (ataque/defensa relativo) ────────────────────────────
    cmp_att = ratios.get("cmp_att_edge", 0)
    cmp_def = ratios.get("cmp_def_edge", 0)
    if "1x" in j or "local" in j or "home" in j:
        if cmp_att > 0.20:
            ajuste += 0.3
            ajustes.append(f"Ataque relativo local superior ({cmp_att:.0%}): +0.30")
        if cmp_def > 0.15:
            ajuste += 0.2
            ajustes.append(f"Defensa relativa local superior ({cmp_def:.0%}): +0.20")

    # ── Field tilt ─────────────────────────────────────────────────────────────
    ft_home = ratios.get("home_field_tilt", 0.5)
    if ft_home > 0.65 and ("1x" in j or "over" in j):
        ajuste += 0.2
        ajustes.append(f"Field tilt local alto ({ft_home:.0%}): +0.20")

    # ── Possession efficiency ──────────────────────────────────────────────────
    pe_home = ratios.get("home_possession_efficiency", 0)
    pe_away = ratios.get("away_possession_efficiency", 0)
    if es_goles and (pe_home + pe_away) > 0.08:  # >0.04 xG por % posesión
        ajuste += 0.15
        ajustes.append("Possession efficiency alta: +0.15")

    # ── VAR home advantage ─────────────────────────────────────────────────────
    if ratios.get("tiene_var") and ("1x" in j or "local" in j):
        ajuste -= 0.1
        ajustes.append("Liga con VAR: home advantage reducido -0.10")

    # ── npxG proxy (penales no repetibles) ────────────────────────────────────
    xg_h_raw = ratios.get("home_xg_pred", 0) or 0
    goles_h = ratios.get("home_goles_favor_prom", 0) or 0
    shots_h_raw = ratios.get("home_shots_total", 1) or 1
    npxg_h = calcular_npxg_proxy(float(xg_h_raw), float(goles_h), float(shots_h_raw))
    if es_goles and abs(npxg_h - float(xg_h_raw)) > 0.3:
        ajuste += (npxg_h - float(xg_h_raw)) * 0.15
        ajustes.append(f"npxG ajuste: {npxg_h:.2f} vs xG {float(xg_h_raw):.2f}")

    # ── Competition xG adjustment ──────────────────────────────────────────────
    factor_comp = ratios.get("factor_xg_competicion", 1.0)
    if factor_comp < 1.0 and es_goles:
        ajuste_comp = (factor_comp - 1.0) * 0.5  # mitad del factor como ajuste de score
        ajuste += ajuste_comp
        ajustes.append(f"Factor competición ({factor_comp}): {ajuste_comp:+.2f}")

    # ── Referee strictness ─────────────────────────────────────────────────────
    if arbitro_perfil and arbitro_perfil.get("conocido"):
        if "tarjeta" in j or "card" in j or "booking" in j:
            if arbitro_perfil["estricto"]:
                ajuste += 0.5
                ajustes.append(f"Árbitro estricto ({arbitro_perfil['yellows_per_game']:.1f} amarillas/pto): +0.50")
            elif arbitro_perfil["permisivo"]:
                ajuste -= 0.4
                ajustes.append(f"Árbitro permisivo ({arbitro_perfil['yellows_per_game']:.1f} amarillas/pto): -0.40")
        if arbitro_perfil.get("home_bias_fuerte") and "x2" in j:
            ajuste -= 0.2
            ajustes.append("Árbitro con home bias fuerte: X2 penalizado -0.20")

    # ── HT scoring rate como confirmador Over 2.5 ─────────────────────────────
    ht_home = ratios.get("home_ht_scoring_rate", 0.5) if "home_ht_scoring_rate" in ratios else 0.5
    ht_away = ratios.get("away_ht_scoring_rate", 0.5) if "away_ht_scoring_rate" in ratios else 0.5
    if es_goles and ht_home > 0.65 and ht_away > 0.65 and "over" in j:
        ajuste += 0.3
        ajustes.append(f"HT scoring rate alto (local {ht_home:.0%}, visita {ht_away:.0%}): +0.30")

    score_final = round(min(10.0, max(0.0, score_base + ajuste)), 1)
    return {"score_final": score_final, "ajuste_total": round(ajuste, 2), "ajustes": ajustes}


def calcular_ensemble_v16(prob_dixon_coles: float, prob_xg_api: float,
                           prob_pinnacle: float,
                           pesos: tuple = (0.40, 0.35, 0.25)) -> float:
    """
    V23: Ensemble de 3 modelos — Dixon-Coles + xG API + Pinnacle devigged.
    Investigación: el promedio de los mejores modelos mejora el TRPS score.
    Pesos por defecto: Dixon-Coles 40%, xG API 35%, Pinnacle 25%.
    Si un modelo no está disponible (0), redistribuir sus pesos.
    """
    probs = [prob_dixon_coles, prob_xg_api, prob_pinnacle]
    w = list(pesos)
    # Excluir modelos sin datos
    disponibles = [(p, ww) for p, ww in zip(probs, w) if p and p > 0]
    if not disponibles:
        return prob_dixon_coles or 50.0
    total_w = sum(ww for _, ww in disponibles)
    ensemble = sum(p * ww for p, ww in disponibles) / total_w
    return round(ensemble, 2)


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 20B — MEJORAS PENDIENTES: RLM, xGA, Kelly, Set Pieces, DNB, Formato48
# ─────────────────────────────────────────────────────────────────────────────

def detectar_rlm(cuota_apertura: float, cuota_actual: float,
                  es_favorito: bool = False) -> dict:
    """
    N10: Reverse Line Movement (RLM).
    Cuota del underdog BAJA >0.15 desde apertura = dinero sharp en el underdog.
    Señal contraria a la intuición — el público apuesta al favorito pero el
    dinero inteligente va al underdog. Bonus +0.3 al score del underdog.

    Retorna: {"rlm": bool, "ajuste_score": float, "motivo": str}
    """
    if not cuota_apertura or not cuota_actual or cuota_apertura <= 1:
        return {"rlm": False, "ajuste_score": 0.0, "motivo": ""}
    cambio = cuota_apertura - cuota_actual  # positivo = cuota bajo = se acorto
    if not es_favorito and cambio >= 0.15:
        return {
            "rlm": True,
            "ajuste_score": 0.3,
            "motivo": f"RLM: cuota underdog bajo {cambio:.2f} desde apertura — dinero sharp confirmado",
        }
    return {"rlm": False, "ajuste_score": 0.0, "motivo": ""}


def calcular_xga_proxy(shots_on_goal_rival: float) -> float:
    """
    N2/Y4: xGA proxy = shots_on_goal del rival × 0.33
    Aproximación de los goles esperados concedidos cuando no hay
    xGA directo disponible en la API.
    """
    return round(max(0.2, shots_on_goal_rival * 0.33), 2)


def kelly_dinamico(prob: float, cuota: float, bank: float,
                    confirmado_pinnacle: bool = False) -> float:
    """
    N14: Kelly dinámico — 1/4 Kelly cuando incertidumbre alta,
    1/2 Kelly cuando confirmado por movimiento Pinnacle.
    Investigación: 1/4 Kelly preserva el bank en picks de convicción media;
    1/2 Kelly es correcto cuando el mercado confirma el edge.
    """
    if prob <= 0 or cuota <= 1:
        return 0.0
    prob_dec = prob / 100
    kelly = (prob_dec * cuota - 1) / (cuota - 1)
    if kelly <= 0:
        return 0.0
    fraccion = 0.50 if confirmado_pinnacle else 0.25
    stake = bank * kelly * fraccion
    return round(max(0.0, stake), 2)


def flag_set_piece_rate(goles_totales: float, shots_on_target: float,
                         goles_corner: float = 0.0) -> dict:
    """
    X8/Y7: Set piece rate — si un equipo marca mucho más de lo que
    sus tiros a puerta justifican, probablemente tiene alta tasa de
    goles de set pieces o penales.
    Ratio > 1.30 → +0.15 xG estimado al atacante.

    Retorna: {"alto": bool, "ajuste_xg": float, "motivo": str}
    """
    if not shots_on_target or shots_on_target <= 0:
        return {"alto": False, "ajuste_xg": 0.0, "motivo": ""}
    # Ratio esperado: ~0.33 goles por tiro a puerta en promedio europeo
    ratio_esperado = shots_on_target * 0.33
    if ratio_esperado <= 0:
        return {"alto": False, "ajuste_xg": 0.0, "motivo": ""}
    ratio = goles_totales / ratio_esperado
    if ratio >= 1.30:
        return {
            "alto": True,
            "ajuste_xg": 0.15,
            "motivo": f"Set piece rate alto ({ratio:.2f}x esperado) — +0.15 xG al ataque",
        }
    return {"alto": False, "ajuste_xg": 0.0, "motivo": ""}


def evaluar_dnb_seleccion(prob_home: float, prob_empate: float,
                           prob_away: float, cuota_dnb: float,
                           diff_ranking_fifa: int) -> dict:
    """
    N11: DNB (Draw No Bet) en eliminatorias de selecciones.
    Tiene valor cuando:
    - Diferencia de ranking FIFA entre 15-35 (no extremo)
    - Cuota DNB >= 1.35
    - El mercado tiene prob de empate >= 20%

    El DNB elimina el riesgo del empate preservando el edge del favorito
    sin pagar la cuota reducida del DC. Especialmente útil en octavos/cuartos.
    Retorna: {"recomendar": bool, "score": float, "motivo": str}
    """
    if diff_ranking_fifa < 15 or diff_ranking_fifa > 35:
        return {"recomendar": False, "score": 0.0,
                "motivo": f"DNB: diff ranking {diff_ranking_fifa} fuera del rango 15-35"}
    if cuota_dnb < 1.35:
        return {"recomendar": False, "score": 0.0,
                "motivo": f"DNB: cuota {cuota_dnb} < 1.35 — sin valor suficiente"}
    if prob_empate < 0.20:
        return {"recomendar": False, "score": 0.0,
                "motivo": f"DNB: prob empate {prob_empate:.0%} < 20% — proteccion innecesaria"}
    ev = prob_home * (cuota_dnb - 1) + prob_empate * 0 + prob_away * (-1)
    score = round(min(9.5, 6.0 + ev * 10), 1)
    return {
        "recomendar": True,
        "score": score,
        "motivo": f"DNB valor: diff FIFA {diff_ranking_fifa}, cuota {cuota_dnb}, "
                  f"empate {prob_empate:.0%} — protege sin pagar prima DC",
    }


def ajuste_formato48_j3(es_j3: bool, necesita_goles: bool,
                          diff_goles_actual: int = 0) -> dict:
    """
    W2: Formato 48 equipos Mundial — en J3, los equipos que necesitan
    mejorar su diferencia de goles para clasificar como mejor tercero
    tienen incentivo extra para atacar → Over 2.5 tiene valor estructural nuevo.
    Los 8 mejores terceros clasifican, muchos equipos luchan por goal difference.
    Retorna: {"bonus_over": bool, "ajuste_score": float, "motivo": str}
    """
    if not es_j3:
        return {"bonus_over": False, "ajuste_score": 0.0, "motivo": ""}
    if necesita_goles:
        return {
            "bonus_over": True,
            "ajuste_score": 0.3,
            "motivo": "W2: Formato 48 J3 — equipo necesita mejorar GD para clasificar como mejor 3ro — Over tiene valor",
        }
    return {"bonus_over": False, "ajuste_score": 0.0,
            "motivo": "W2: J3 pero ambos equipos ya clasificados o eliminados — partido de bajo riesgo"}



# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 20C — GRUPO 1: Alto impacto, baja complejidad
# W4, W9, W10, W12, W13, D3, D4, O10, P4, DC10, Z14, Z23
# ─────────────────────────────────────────────────────────────────────────────

def evaluar_motivacion_j3(ya_clasificado_home: bool, ya_clasificado_away: bool,
                           eliminado_home: bool, eliminado_away: bool) -> dict:
    """
    W4: Factor motivacion en J3 del Mundial.
    Escenarios criticos:
    - Ambos clasificados → partido relajado, rotaciones, Under 2.5 valor
    - Ambos eliminados → partido sin presion, impredecible, evitar
    - Uno necesita ganar → partido abierto, Over 2.5 valor
    - Uno clasifica con empate → partido conservador, DC del que necesita menos
    """
    if ya_clasificado_home and ya_clasificado_away:
        return {
            "escenario": "ambos_clasificados",
            "ajuste_score": -0.5,
            "mercado_recomendado": "Under 2.5",
            "motivo": "W4: Ambos clasificados — rotaciones y bajo incentivo → Under 2.5",
        }
    if eliminado_home and eliminado_away:
        return {
            "escenario": "ambos_eliminados",
            "ajuste_score": -1.0,
            "mercado_recomendado": "evitar",
            "motivo": "W4: Ambos eliminados — partido sin presion, resultado impredecible → evitar",
        }
    if (ya_clasificado_home and not ya_clasificado_away) or        (ya_clasificado_away and not ya_clasificado_home):
        return {
            "escenario": "uno_clasificado",
            "ajuste_score": +0.3,
            "mercado_recomendado": "Over 2.5",
            "motivo": "W4: Un equipo necesita resultado — partido abierto → Over 2.5 valor",
        }
    return {
        "escenario": "ambos_en_juego",
        "ajuste_score": +0.2,
        "mercado_recomendado": "normal",
        "motivo": "W4: Ambos equipos se juegan algo → partido de alta intensidad",
    }


def evaluar_rebote_emocional_j2(perdio_j1_home: bool, perdio_j1_away: bool) -> dict:
    """
    W10: Rebote emocional en J2 tras derrota en J1.
    Equipos que perdieron J1 tienen mayor motivacion en J2 → Over 2.5 mas probable.
    Historicamente J2 tiene 2.94 goles/partido (el mas alto del torneo).
    Combinacion: derrota J1 + J2 = señal Over muy fuerte.
    """
    if perdio_j1_home and perdio_j1_away:
        return {
            "señal": "over_fuerte",
            "ajuste_score": +0.5,
            "motivo": "W10: Ambos perdieron J1 — doble rebote emocional, J2=2.94 goles/pto → Over fuerte",
        }
    if perdio_j1_home or perdio_j1_away:
        perdedor = "Local" if perdio_j1_home else "Visitante"
        return {
            "señal": "over_moderado",
            "ajuste_score": +0.3,
            "motivo": f"W10: {perdedor} perdio J1 — rebote emocional esperado en J2 → Over moderado",
        }
    return {"señal": "neutral", "ajuste_score": 0.0, "motivo": ""}


def detectar_draw_tactico_j3(ya_clasificado_home: bool, ya_clasificado_away: bool,
                              resultado_sirve_empate_home: bool,
                              resultado_sirve_empate_away: bool) -> dict:
    """
    W12: Draws tacticos en J3 cuando a ambos equipos les sirve el empate.
    Historicamente en estos partidos el empate ocurre con frecuencia anormal.
    El mercado no descuenta completamente este factor → empate directo con valor.
    """
    if resultado_sirve_empate_home and resultado_sirve_empate_away:
        return {
            "draw_tactico": True,
            "ajuste_score_empate": +1.5,
            "motivo": "W12: Draw tactico J3 — a ambos les sirve el empate → empate directo con valor anormal",
        }
    if resultado_sirve_empate_home or resultado_sirve_empate_away:
        return {
            "draw_tactico": False,
            "ajuste_score_empate": +0.3,
            "motivo": "W12: A uno le sirve el empate — partido conservador esperado",
        }
    return {"draw_tactico": False, "ajuste_score_empate": 0.0, "motivo": ""}


def evaluar_under10_primer_tiempo_j1(es_j1: bool, estilo_home: str,
                                      estilo_away: str) -> dict:
    """
    W13: Under 1.0 primer tiempo en J1.
    J1 historicamente tiene 2.38 goles/partido en total, pero el primer tiempo
    es significativamente mas bajo (equipos cautos, no conocen al rival en el torneo).
    Si ambos equipos tienen estilo defensivo → Under 0.5 HT valor extremo.
    """
    if not es_j1:
        return {"recomendar": False, "motivo": ""}
    if estilo_home == "defensivo" and estilo_away == "defensivo":
        return {
            "recomendar": True,
            "jugada": "Under 0.5 primer tiempo",
            "score": 8.0,
            "motivo": "W13: J1 + ambos defensivos — primer tiempo muy cerrado, Under 0.5 HT valor",
        }
    return {
        "recomendar": True,
        "jugada": "Under 1.0 primer tiempo",
        "score": 7.5,
        "motivo": "W13: J1 — equipos cautelosos en primer partido del torneo, Under 1.0 HT historico",
    }


def veto_score_minimo_global(score: float, umbral: float = 7.0) -> bool:
    """
    D3: Veto automatico si score < 7.0 independiente del mercado.
    Ningun pick deberia emitirse con score menor a este umbral global,
    independientemente de que cumpla criterios individuales del mercado.
    """
    return score < umbral


def verificar_limite_picks_mercado(picks_dia: list, mercado: str,
                                    max_por_mercado: int = 2) -> bool:
    """
    D4: Limite diario de picks por mercado.
    Evita sobreexposicion en un solo mercado aunque haya muchas señales.
    Maximo 2 picks de Over 2.5, 2 de DC, 2 de AH, etc. por dia.
    Retorna True si el mercado ya alcanzo el limite (veto).
    """
    picks_mercado = [p for p in picks_dia
                     if p.get("mercado", "").lower() == mercado.lower()]
    return len(picks_mercado) >= max_por_mercado


def detectar_racha_under25(resultados_under_home: list,
                            resultados_under_away: list) -> dict:
    """
    O10: Under 2.5 racha >= 4 partidos consecutivos → señal fuerte.
    Si ambos equipos llevan 4+ partidos seguidos Under 2.5 en sus roles,
    la señal es muy robusta independientemente del xG del modelo.
    """
    def contar_racha(resultados: list) -> int:
        racha = 0
        for r in reversed(resultados):
            if r is True:  # Under 2.5 = True
                racha += 1
            else:
                break
        return racha

    racha_home = contar_racha(resultados_under_home)
    racha_away = contar_racha(resultados_under_away)

    if racha_home >= 4 and racha_away >= 4:
        return {
            "señal": "under_fuerte",
            "score_bonus": 1.2,
            "motivo": f"O10: Racha Under 2.5 — local {racha_home} seguidos, visitante {racha_away} → señal muy fuerte",
        }
    if racha_home >= 4 or racha_away >= 4:
        equipo = "Local" if racha_home >= 4 else "Visitante"
        racha = max(racha_home, racha_away)
        return {
            "señal": "under_moderado",
            "score_bonus": 0.5,
            "motivo": f"O10: {equipo} lleva {racha} partidos consecutivos Under 2.5 → señal moderada",
        }
    return {"señal": "neutral", "score_bonus": 0.0, "motivo": ""}


def veto_zona_peligro_mundial(cuota_favorito: float, es_mundial: bool) -> dict:
    """
    P4: Zona de peligro Mundial — favoritos 1.30-1.60 tienen ROI -25%.
    Analisis historico de 2 Mundiales: los favoritos en este rango de cuota
    son los mas sobrevaluados por el mercado. El publico paga demasiado por la
    "seguridad" que parecen ofrecer. Los tipsters profesionales evitan este rango.
    Aplica a picks 1X2 directos (no a DC ni AH).
    """
    if not es_mundial:
        return {"vetar": False, "motivo": ""}
    if 1.30 <= cuota_favorito <= 1.60:
        return {
            "vetar": True,
            "motivo": f"P4: Zona peligro Mundial — favorito a {cuota_favorito} (rango 1.30-1.60) tiene ROI -25% historico. Preferir DC o AH.",
        }
    return {"vetar": False, "motivo": ""}


def preferir_dc_sobre_1x2_mundial(cuota_1x2: float, cuota_dc: float,
                                   diff_elo: int, es_mundial: bool) -> dict:
    """
    DC10: En Mundial con diferencia clara, DC es preferible sobre 1X2.
    El DC elimina el riesgo del empate sin pagar tanto margen como el 1X2.
    Especialmente valido cuando:
    - diff Elo > 100 (hay diferencia real de nivel)
    - cuota 1X2 esta en zona peligro (1.30-1.60)
    - cuota DC tiene valor (>= 1.20)
    """
    if not es_mundial:
        return {"preferir_dc": False, "motivo": ""}
    if diff_elo > 100 and 1.30 <= cuota_1x2 <= 1.70 and cuota_dc >= 1.20:
        return {
            "preferir_dc": True,
            "motivo": f"DC10: Mundial diff Elo {diff_elo} — DC {cuota_dc} preferible sobre 1X2 {cuota_1x2} por zona peligro",
        }
    return {"preferir_dc": False, "motivo": ""}


def ajuste_ah_home_away_split(xg_home_en_casa: float, xg_away_de_visita: float,
                               es_local: bool) -> dict:
    """
    Z14: Home/away split para AH.
    La misma linea AH no aplica igual cuando el equipo juega en casa vs de visita.
    Un equipo con xG 2.0 en casa pero solo 1.2 de visita NO deberia recibir
    la misma linea AH -0.5 en ambas situaciones.
    """
    if es_local:
        xg_ref = xg_home_en_casa
        contexto = "en casa"
    else:
        xg_ref = xg_away_de_visita
        contexto = "de visita"

    diff_split = xg_home_en_casa - xg_away_de_visita
    if abs(diff_split) >= 0.5:
        return {
            "ajuste_necesario": True,
            "xg_contextual": xg_ref,
            "motivo": f"Z14: Split home/away significativo (diff {diff_split:.1f}) — usar xG {contexto} ({xg_ref:.1f}) para calcular linea AH",
        }
    return {
        "ajuste_necesario": False,
        "xg_contextual": xg_ref,
        "motivo": "",
    }


def evaluar_goal_expectancy_over15(xg_combinado: float,
                                    scoring_rate_home: float,
                                    scoring_rate_away: float) -> dict:
    """
    Z23: Goal expectancy >= 2.76 → seleccion ideal para Over 1.5.
    Este umbral especifico esta validado empiricamente por traders de FTS:
    cuando el modelo espera >= 2.76 goles combinados, Over 1.5 tiene
    EV positivo incluso a cuotas de 1.25-1.35.
    EPL 2025-26 promedia 2.77 goles/partido → Over 1.5 ~80% hit rate estructural.
    """
    if xg_combinado >= 2.76:
        score_bonus = 0.4
        motivo = f"Z23: Goal expectancy {xg_combinado:.2f} >= 2.76 — zona ideal Over 1.5, EV positivo incluso a 1.25"
    elif xg_combinado >= 2.50:
        score_bonus = 0.2
        motivo = f"Z23: Goal expectancy {xg_combinado:.2f} — Over 1.5 probable"
    else:
        score_bonus = 0.0
        motivo = ""

    # Bonus adicional si scoring rate de ambos es alto
    if scoring_rate_home >= 75 and scoring_rate_away >= 75:
        score_bonus += 0.2
        motivo += " | Ambos con scoring rate >=75% — Over 1.5 muy confiable"

    return {
        "score_bonus": round(score_bonus, 2),
        "motivo": motivo,
        "zona_ideal": xg_combinado >= 2.76,
    }



# ═════════════════════════════════════════════════════════════════════════════
# SECCIÓN 20D — 37 MEJORAS FACTIBLES RESTANTES
# M3, M5, M7, W6-W7, W11, W14, D2, D5-D8, O1, O7-O8, O12,
# DC7-DC8, AH2, NM4-NM5, CQ5-CQ6, CQ10, N2, N8, P1, P5-P7,
# P11-P12, P14, Z2, Z12, Z15, Z24
# ═════════════════════════════════════════════════════════════════════════════

# ── M3: xGD acumulado como feature Dixon-Coles ───────────────────────────────
def calcular_xgd_acumulado(fixtures: list, team_id: int) -> float:
    """
    M3: xGD = suma(xG_favor - xG_contra) en los últimos N partidos.
    Equipos con xGD alto pero pocos puntos = underperforming (bonus).
    Equipos con xGD bajo pero muchos puntos = overperforming (penalizar).
    Usar xg_pred de la API cuando esté disponible; sino estimar desde goles.
    """
    xgd = 0.0
    for m in (fixtures or []):
        es_local = m.get("teams", {}).get("home", {}).get("id") == team_id
        xg_h = float(m.get("score", {}).get("extratime", {}).get("home") or
                     m.get("goals", {}).get("home") or 0)
        xg_a = float(m.get("score", {}).get("extratime", {}).get("away") or
                     m.get("goals", {}).get("away") or 0)
        if es_local:
            xgd += xg_h - xg_a
        else:
            xgd += xg_a - xg_h
    return round(xgd, 2)

def ajuste_score_xgd(xgd_home: float, xgd_away: float, jugada: str) -> float:
    """
    M3: Ajuste de score basado en xGD acumulado.
    xGD muy positivo del favorito = mayor dominancia real → +0.2 en picks de ese equipo.
    xGD muy negativo = equipo en problemas reales → -0.2.
    """
    j = jugada.lower()
    es_pick_home = any(x in j for x in ["1x", "victoria local", "home"])
    es_pick_away = any(x in j for x in ["x2", "victoria visitante", "away"])
    ajuste = 0.0
    if es_pick_home:
        if xgd_home >= 3.0: ajuste += 0.2
        elif xgd_home <= -3.0: ajuste -= 0.2
    if es_pick_away:
        if xgd_away >= 3.0: ajuste += 0.2
        elif xgd_away <= -3.0: ajuste -= 0.2
    return round(ajuste, 2)


# ── M5: Ventana rolling 90 días ───────────────────────────────────────────────
def calcular_last_n_desde_fecha(fecha_partido: str, dias: int = 90) -> int:
    """
    M5: Convierte una ventana de 90 días a número aproximado de partidos.
    Equipos de liga top juegan ~3-4 partidos/mes = ~8-12 partidos en 90 días.
    Equipos de selección: mucho menos (~4-6 en 90 días).
    Retorna el last=N que aproxima los 90 días.
    """
    try:
        from datetime import datetime as _dt
        fecha = _dt.strptime(fecha_partido[:10], "%Y-%m-%d")
        dias_desde = (datetime.utcnow() - fecha).days
        partidos_estimados = max(5, min(15, int(dias / 7.5)))
        return partidos_estimados
    except Exception:
        return 10  # fallback seguro


# ── M7: Top 15% EV histórico ─────────────────────────────────────────────────
def es_top15_ev(ev_actual: float, historial_ev: list) -> bool:
    """
    M7: Solo emitir pick si el EV está en el top 15% del historial propio.
    Evita picks mediocres que cumplen el umbral mínimo pero no son los mejores.
    historial_ev: lista de EVs de picks anteriores del mismo mercado.
    """
    if not historial_ev or len(historial_ev) < 10:
        return True  # sin historial suficiente: no filtrar
    umbral = sorted(historial_ev, reverse=True)[int(len(historial_ev) * 0.15)]
    return ev_actual >= max(umbral, 0.03)  # mínimo 3% EV siempre


# ── N2: De-vig Pinnacle método aditivo ───────────────────────────────────────
def devig_pinnacle_aditivo(cuota_home: float, cuota_draw: float,
                            cuota_away: float) -> dict:
    """
    N2: Elimina el margen (vig) de Pinnacle usando método aditivo.
    Más preciso que el método multiplicativo para cuotas cercanas.
    Retorna probabilidades reales sin margen para comparar con el modelo.
    """
    try:
        if not all([cuota_home, cuota_draw, cuota_away]):
            return {}
        # Probabilidades brutas (con vig)
        p_h = 1 / cuota_home
        p_d = 1 / cuota_draw
        p_a = 1 / cuota_away
        total = p_h + p_d + p_a
        margen = total - 1.0
        # Método aditivo: restar margen proporcional a cada probabilidad
        p_h_real = p_h - (margen * p_h / total)
        p_d_real = p_d - (margen * p_d / total)
        p_a_real = p_a - (margen * p_a / total)
        return {
            "prob_home": round(p_h_real * 100, 2),
            "prob_draw": round(p_d_real * 100, 2),
            "prob_away": round(p_a_real * 100, 2),
            "margen_pct": round(margen * 100, 2),
            "cuota_justa_home": round(1 / p_h_real, 3),
            "cuota_justa_draw": round(1 / p_d_real, 3),
            "cuota_justa_away": round(1 / p_a_real, 3),
        }
    except Exception:
        return {}


# ── O1: Umbral Over 2.5 dinámico por liga ────────────────────────────────────
UMBRAL_OVER25_POR_LIGA = {
    # Ligas con muchos goles → umbral más exigente para Over (ya común)
    "bundesliga":         {"over25_base": 62, "under25_base": 38},
    "eredivisie":         {"over25_base": 60, "under25_base": 40},
    "premier league":     {"over25_base": 58, "under25_base": 42},
    # Ligas equilibradas
    "ligue 1":            {"over25_base": 52, "under25_base": 48},
    "serie a":            {"over25_base": 50, "under25_base": 50},
    "serie a italia":     {"over25_base": 50, "under25_base": 50},
    # Ligas defensivas → umbral más bajo para Over (es difícil alcanzar)
    "la liga":            {"over25_base": 48, "under25_base": 52},
    "laliga":             {"over25_base": 48, "under25_base": 52},
    # Mundial grupos
    "fifa world cup":     {"over25_base": 45, "under25_base": 55},
    "world cup":          {"over25_base": 45, "under25_base": 55},
}

def umbral_over25_dinamico(liga: str, mercado: str = "over") -> float:
    """
    O1: Umbral dinámico Over/Under 2.5 por liga.
    En Bundesliga, Over 2.5 ocurre 62% → necesitas prob modelo ≥67% para tener edge.
    En La Liga, Over 2.5 ocurre 48% → necesitas prob modelo ≥53% para edge.
    """
    datos = UMBRAL_OVER25_POR_LIGA.get(liga.lower(), {"over25_base": 52, "under25_base": 48})
    if mercado == "over":
        base = datos["over25_base"]
        return base + 5  # necesitas superar el baseline + 5% para EV positivo
    else:
        base = datos["under25_base"]
        return base + 5


# ── O7/P1: Líneas asiáticas 2.25/2.75 para zona gris ────────────────────────
def recomendar_linea_asiatica_goles(xg_combinado: float,
                                     liga: str = "") -> dict:
    """
    O7/P1: Cuando el xG está en zona gris (2.2-2.8), las líneas asiáticas
    2.25 y 2.75 reducen varianza vs las líneas enteras 2.5 y 3.0.
    - xG 2.0-2.4: Over 2.25 (ganas todo si ≥3 goles, mitad si exactamente 2)
    - xG 2.4-2.6: zona exactamente gris → Over 2.5 o Under 2.5 con mayor margen
    - xG 2.6-3.0: Over 2.75 (ganas todo si ≥3 goles, mitad si exactamente 3)
    - xG 3.0-3.5: Over 3.25 (menos riesgo que Over 3.5 entero)
    """
    if 2.0 <= xg_combinado < 2.4:
        return {
            "linea_recomendada": "Over 2.25 (asiática)",
            "descripcion": "Zona gris baja — Over 2.25 protege el empate en 2 goles",
            "ev_mejorado": True,
        }
    elif 2.4 <= xg_combinado < 2.6:
        return {
            "linea_recomendada": "Over 2.5 con margen extra o evitar",
            "descripcion": "Zona gris central — esperar mejor oportunidad o exigir mayor prob",
            "ev_mejorado": False,
        }
    elif 2.6 <= xg_combinado < 3.0:
        return {
            "linea_recomendada": "Over 2.75 (asiática)",
            "descripcion": "Zona gris alta — Over 2.75 protege si hay exactamente 3 goles",
            "ev_mejorado": True,
        }
    elif 3.0 <= xg_combinado < 3.5:
        return {
            "linea_recomendada": "Over 3.25 (asiática)",
            "descripcion": "xG alto — Over 3.25 menos riesgo que Over 3.5 entero",
            "ev_mejorado": True,
        }
    return {"linea_recomendada": None, "descripcion": "Sin zona gris detectada", "ev_mejorado": False}


# ── O8/NM4/P11: BTTS-No en mismatches ────────────────────────────────────────
def evaluar_btts_no(clean_sheet_home: float, clean_sheet_away: float,
                    failed_to_score_away: float, diff_ranking: int = 0) -> dict:
    """
    O8/NM4/P11: BTTS-No (al menos un equipo NO marca) en mismatches claros.
    Criterios: favorito tiene clean sheet ≥40% + underdog tiene failed to score ≥35%.
    Cuota típica de BTTS-No: 1.50-1.70 → EV positivo cuando prob real ≥60%.
    """
    prob_btts_no = 0.0
    motivos = []
    # Prob que el favorito no reciba: clean sheet rate
    prob_no_concede_home = clean_sheet_home / 100
    # Prob que el visitante no marque: failed to score rate
    prob_no_marca_away = failed_to_score_away / 100
    # BTTS-No = (no marca home) OR (no marca away) ≈ 1 - P(ambos marcan)
    prob_btts = (1 - prob_no_concede_home) * (1 - prob_no_marca_away)
    prob_btts_no = round((1 - prob_btts) * 100, 1)

    if clean_sheet_home >= 40:
        motivos.append(f"Clean sheet local {clean_sheet_home:.0f}% — defiende bien")
    if failed_to_score_away >= 35:
        motivos.append(f"Visitante no marca en {failed_to_score_away:.0f}% visitas")
    if diff_ranking >= 15:
        prob_btts_no = min(prob_btts_no + 5, 85)
        motivos.append(f"Mismatch ranking {diff_ranking} — underdog raramente marca")

    recomendar = prob_btts_no >= 60 and clean_sheet_home >= 35 and failed_to_score_away >= 30
    score = round(min(9.5, 5.0 + prob_btts_no / 15), 1) if recomendar else 0.0

    return {
        "recomendar": recomendar,
        "prob_btts_no": prob_btts_no,
        "score": score,
        "motivos": motivos,
    }


# ── O12/P12: Mismatch Mundial Over 3.5 ───────────────────────────────────────
def evaluar_mismatch_over35_mundial(diff_ranking_fifa: int, btts_rate_underdog: float,
                                     xg_combinado: float, es_mundial: bool) -> dict:
    """
    O12/P12: Mismatch claro en Mundial + underdog tiene BTTS rate >25% → Over 3.5.
    Lógica: el favorito gana 3-4-0 mientras el underdog intenta marcar.
    Condiciones: diff FIFA >350pts (aprox diff ranking >20), underdog BTTS >25%.
    """
    if not es_mundial:
        return {"recomendar": False, "motivo": ""}
    diff_elo_aprox = diff_ranking_fifa * 3
    if diff_elo_aprox >= 300 and btts_rate_underdog >= 25 and xg_combinado >= 3.0:
        return {
            "recomendar": True,
            "score": round(min(9.0, 5.0 + diff_elo_aprox / 200), 1),
            "motivo": f"O12: Mismatch Mundial diff~{diff_elo_aprox}Elo + underdog BTTS {btts_rate_underdog:.0f}% → Over 3.5",
        }
    return {"recomendar": False, "motivo": ""}


# ── DC7/P14: Away favorite bias ───────────────────────────────────────────────
def evaluar_away_favorite_dc(cuota_favorito_visitante: float, liga: str) -> dict:
    """
    DC7/P14: Away favorite bias — cuando el favorito juega de visita a cuota ≤1.70,
    el mercado tiende a sobreestimar sus posibilidades. El DC 1X del local
    (favorito en casa) tiene más valor estructural que apostar al visitante directo.
    Especialmente pronunciado en La Liga, Serie A, Ligue 1.
    """
    ligas_bias = {"la liga", "laliga", "serie a", "serie a italia", "ligue 1"}
    if cuota_favorito_visitante is None:
        return {"dc_1x_valor": False, "motivo": ""}
    if float(cuota_favorito_visitante) <= 1.70 and liga.lower() in ligas_bias:
        return {
            "dc_1x_valor": True,
            "ajuste_score": 0.3,
            "motivo": f"DC7/P14: Away favorite bias en {liga} — favorito visitante {cuota_favorito_visitante} ≤1.70 → DC 1X del local con valor",
        }
    return {"dc_1x_valor": False, "motivo": ""}


# ── DC8: Veto DC en amistosos ─────────────────────────────────────────────────
def veto_dc_amistoso(liga: str) -> bool:
    """
    DC8: Veto DC en amistosos y partidos de preparación.
    En amistosos hay rotaciones masivas, resultado no importa → DC pierde valor real.
    """
    l = liga.lower()
    return any(x in l for x in ["friendl", "amistoso", "preparacion",
                                  "test match", "international friendly"])


# ── AH2: Eficiencia ofensiva ajusta línea AH ─────────────────────────────────
def ajustar_linea_ah_por_eficiencia(linea_base: str, eficiencia: float) -> str:
    """
    AH2/Z12: Si un equipo tiene eficiencia ofensiva baja (<0.80),
    usar línea AH más conservadora (un escalón menos agresivo).
    Si tiene eficiencia alta (>1.20), la línea base puede ser correcta o más.
    """
    orden = ["AH(+0.75)+", "AH(+0.5)", "AH(+0.25)", "AH(0)",
             "AH(-0.25)", "AH(-0.5)", "AH(-0.75)", "AH(-1.0)", "AH(-1.25)", "AH(-1.5)+"]
    try:
        idx = next(i for i, x in enumerate(orden) if x == linea_base)
        if eficiencia < 0.80:
            # Eficiencia baja → línea un escalón menos agresiva (más hacia AH(0))
            nuevo_idx = max(0, idx - 1)
            return orden[nuevo_idx]
        elif eficiencia > 1.20:
            # Eficiencia alta → mantener o aumentar un escalón
            nuevo_idx = min(len(orden) - 1, idx + 1)
            return orden[nuevo_idx]
    except StopIteration:
        pass
    return linea_base


# ── NM5: Under 3.5 semis y finales Mundial ────────────────────────────────────
PROB_UNDER35_FASE_MUNDIAL = {
    "group":       45,  # grupos: partidos más abiertos
    "round_of_16": 52,
    "quarter":     60,
    "semi":        68,  # semis: muy conservadores
    "final":       72,  # final: el partido más cerrado históricamente
}

def prob_under35_por_fase(fase: str) -> int:
    """NM5: Probabilidad base de Under 3.5 según fase del Mundial."""
    return PROB_UNDER35_FASE_MUNDIAL.get(fase, 52)


# ── CQ5/P7: Correcto resultado como eslabón ───────────────────────────────────
RESULTADOS_FRECUENTES_POR_LIGA = {
    "premier league":  [("1-0", 0.14), ("1-1", 0.12), ("2-1", 0.11), ("2-0", 0.10)],
    "la liga":         [("1-0", 0.16), ("1-1", 0.13), ("2-0", 0.11), ("0-0", 0.09)],
    "laliga":          [("1-0", 0.16), ("1-1", 0.13), ("2-0", 0.11), ("0-0", 0.09)],
    "bundesliga":      [("2-1", 0.13), ("1-0", 0.12), ("3-1", 0.10), ("2-0", 0.09)],
    "serie a":         [("1-0", 0.15), ("0-0", 0.12), ("1-1", 0.12), ("2-0", 0.10)],
    "serie a italia":  [("1-0", 0.15), ("0-0", 0.12), ("1-1", 0.12), ("2-0", 0.10)],
    "ligue 1":         [("1-0", 0.14), ("1-1", 0.12), ("2-1", 0.11), ("2-0", 0.10)],
    "fifa world cup":  [("1-0", 0.18), ("2-0", 0.12), ("1-1", 0.11), ("2-1", 0.10)],
    "world cup":       [("1-0", 0.18), ("2-0", 0.12), ("1-1", 0.11), ("2-1", 0.10)],
}

def recomendar_correcto_resultado(liga: str, prob_home_win: float,
                                   total_prom: float) -> dict:
    """
    CQ5/P7: Correcto resultado más probable como eslabón de alta cuota en tickets.
    Cuotas típicas: 1-0 ~5.00-6.00, 2-1 ~7.00-9.00 → EV positivo en tickets si prob real >15%.
    Solo recomendar como eslabón adicional, nunca como pick principal.
    """
    resultados = RESULTADOS_FRECUENTES_POR_LIGA.get(liga.lower(), [("1-0", 0.13), ("1-1", 0.12)])
    if not resultados:
        return {}
    # Filtrar resultados consistentes con la prob de victoria local
    if prob_home_win >= 55:
        candidatos = [(r, p) for r, p in resultados if not r.startswith("0-")]
    elif prob_home_win <= 40:
        candidatos = [(r, p) for r, p in resultados if r.startswith("0-") or "-0" in r[2:]]
    else:
        candidatos = resultados[:2]
    if not candidatos:
        candidatos = resultados[:1]
    mejor = candidatos[0]
    return {
        "resultado": mejor[0],
        "prob_estimada": round(mejor[1] * 100, 1),
        "uso": "eslabón ticket alta cuota — no pick principal",
    }


# ── CQ10: EV compuesto por ticket completo ────────────────────────────────────
def calcular_ev_compuesto_ticket(picks: list) -> dict:
    """
    CQ10: EV compuesto del ticket completo.
    EV_ticket = (prob1 × prob2 × ... × probN) × cuota_total - 1
    Un ticket puede tener EV positivo aunque individualmente los eslabones
    sean marginales, si hay suficiente cuota total.
    """
    if not picks:
        return {"ev": 0.0, "prob_conjunta": 0.0, "cuota_total": 1.0}
    prob_conjunta = 1.0
    cuota_total = 1.0
    for pick in picks:
        prob = float(pick.get("prob", 50)) / 100
        cuota = float(pick.get("cuota", 1.5))
        prob_conjunta *= prob
        cuota_total *= cuota
    ev = prob_conjunta * cuota_total - 1
    return {
        "ev": round(ev, 4),
        "ev_pct": round(ev * 100, 2),
        "prob_conjunta": round(prob_conjunta * 100, 2),
        "cuota_total": round(cuota_total, 3),
        "positivo": ev > 0,
    }


# ── N8: Under 2.5 baseline grupos Mundial ────────────────────────────────────
def ajuste_under25_grupos_mundial(es_mundial: bool, fase: str,
                                   prob_under25_actual: float) -> float:
    """
    N8: Under 2.5 tiene hit rate estructural ~55% en grupos del Mundial
    (vs ~52% promedio general). Si el modelo da prob ≥55% → bonus +0.3 score.
    Dato: últimos 4 Mundiales, 55.2% de partidos de grupos terminaron Under 2.5.
    """
    if not es_mundial or fase != "group":
        return 0.0
    if prob_under25_actual >= 55:
        return 0.3  # Confirmado por histórico → bonus
    elif prob_under25_actual >= 50:
        return 0.1  # Zona gris, leve bonus
    return 0.0


# ── P5: Upsets grupo stage 35% → DC underdog ─────────────────────────────────
def evaluar_upset_dc_underdog(cuota_underdog: float, diff_elo_aprox: int,
                               fase: str, es_mundial: bool) -> dict:
    """
    P5: En grupos del Mundial, el underdog ganó o empató el 35% de partidos
    cuando diff Elo era 100-250 puntos. El mercado sobrevalora al favorito leve.
    DC del underdog (X2) tiene valor cuando cuota X2 ≥ 1.35.
    """
    if not es_mundial or fase != "group":
        return {"recomendar": False, "motivo": ""}
    if 100 <= diff_elo_aprox <= 250 and cuota_underdog is not None:
        cuota_u = float(cuota_underdog)
        if cuota_u >= 2.20:  # underdog razonable
            prob_dc_estimada = 35 + max(0, (250 - diff_elo_aprox) / 5)
            return {
                "recomendar": True,
                "prob_dc_underdog": round(prob_dc_estimada, 1),
                "motivo": f"P5: Upsets grupo Mundial 35% con diff ~{diff_elo_aprox}Elo — DC X2 underdog con valor",
            }
    return {"recomendar": False, "motivo": ""}


# ── P6: Señales live calculables prematch ─────────────────────────────────────
def calcular_señales_live_prematch(prob_home: float, prob_draw: float,
                                    prob_away: float, cuota_home: float,
                                    cuota_away: float) -> dict:
    """
    P6: Calcular qué señales live serán valiosas ANTES del partido.
    Si el favorito va perdiendo <20min → cuota del favorito sube bruscamente
    → hay valor en apostar al favorito live (buy the dip).
    Umbral: favorito con prob >60% que va perdiendo tiene expected recovery rate alto.
    """
    prob_fav = max(prob_home, prob_away)
    es_local_fav = prob_home > prob_away
    cuota_fav = cuota_home if es_local_fav else cuota_away

    señales = []
    if prob_fav >= 60:
        cuota_live_estimada = cuota_fav * 2.2  # si va perdiendo: cuota ~2.2x más alta
        señales.append({
            "señal": "favorito_va_perdiendo_pronto",
            "cuota_live_estimada": round(cuota_live_estimada, 2),
            "motivo": f"P6: Si {'local' if es_local_fav else 'visitante'} (prob {prob_fav:.0f}%) va perdiendo <20' → cuota live ~{cuota_live_estimada:.2f} con valor",
        })
    return {"señales_live": señales}


# ── Z2: Ambos marcaron últimos 5 en roles ────────────────────────────────────
def confirmar_btts_ambos_marcaron(scored_home_pct: float,
                                   scored_away_pct: float) -> dict:
    """
    Z2: Si el local marcó en 80%+ de partidos en casa Y el visitante marcó en
    80%+ de visitas → BTTS muy probable → confirmador de Over 2.5.
    Diferente a BTTS directo: este criterio refuerza Over 2.5, no BTTS.
    """
    if scored_home_pct >= 80 and scored_away_pct >= 80:
        return {
            "confirmador_over": True,
            "score_bonus": 0.5,
            "motivo": f"Z2: Ambos marcan siempre — local {scored_home_pct:.0f}% en casa, visitante {scored_away_pct:.0f}% de visita → Over 2.5 fuerte",
        }
    elif scored_home_pct >= 70 and scored_away_pct >= 70:
        return {
            "confirmador_over": True,
            "score_bonus": 0.2,
            "motivo": f"Z2: Ambos marcan frecuentemente — Over 2.5 confirmado",
        }
    return {"confirmador_over": False, "score_bonus": 0.0, "motivo": ""}


# ── Z15: AH preferible sobre DC en Mundial ────────────────────────────────────
def preferir_ah_sobre_dc_mundial(xg_diff: float, es_mundial: bool,
                                  cuota_dc: float, cuota_ah: float) -> dict:
    """
    Z15: En Mundial, cuando hay diferencia clara (xG diff >0.6),
    el AH ofrece mejor EV que el DC porque:
    - Elimina el empate igual que el DC
    - Tiene menor margen de la casa (Pinnacle AH ~2-3% vs DC ~4-5%)
    - Permite ganar más si el favorito domina ampliamente
    """
    if not es_mundial or xg_diff < 0.6:
        return {"preferir_ah": False, "motivo": ""}
    if cuota_ah and cuota_dc and float(cuota_ah) > float(cuota_dc) * 0.95:
        return {
            "preferir_ah": True,
            "motivo": f"Z15: Mundial xG diff {xg_diff:.1f} — AH {cuota_ah} preferible sobre DC {cuota_dc} (menor margen)",
        }
    return {"preferir_ah": False, "motivo": ""}


# ── Z24: EPL baseline Over 1.5 ───────────────────────────────────────────────
def ajuste_epl_over15(liga: str, prob_over15_actual: float) -> float:
    """
    Z24: EPL 2025-26 promedia 2.77 goles/partido → Over 1.5 ~80% hit rate.
    Si el modelo da prob ≥72% en EPL → bonus +0.2 por el baseline estructural.
    """
    if liga.lower() in ("premier league",) and prob_over15_actual >= 72:
        return 0.2
    return 0.0


# ── D5: Flag alta confianza en mensajes ──────────────────────────────────────
def badge_confianza(score: float) -> str:
    """
    D5: Badge visual para mensajes Telegram según nivel de confianza.
    Permite al usuario identificar rápidamente los picks elite.
    """
    if score >= 9.5: return "🔥🔥 ELITE MÁXIMO"
    if score >= 9.0: return "🔥 ELITE"
    if score >= 8.5: return "⭐⭐ ALTA CONFIANZA"
    if score >= 8.0: return "⭐ CONFIANZA"
    if score >= 7.5: return "📊 ESTÁNDAR"
    return "📋 BÁSICO"


# ── D6: Alerta score 9.5+ ────────────────────────────────────────────────────
def es_alerta_elite(score: float, umbral: float = 9.5) -> bool:
    """D6: Retorna True si el pick merece alerta especial por score muy alto."""
    return float(score) >= umbral


# ── D7: Veto combinadas mismo partido correladas ─────────────────────────────
def veto_mismos_partidos_combinada(picks_combinada: list,
                                    max_mismo_fixture: int = 1) -> bool:
    """
    D7: No combinar más de 1 pick del mismo partido en una combinada.
    Picks del mismo partido están correlados → la multiplicación de probs
    no es independiente → EV calculado es incorrecto.
    """
    from collections import Counter
    fixture_ids = [p.get("fixture_id") for p in picks_combinada if p.get("fixture_id")]
    conteo = Counter(fixture_ids)
    return any(v > max_mismo_fixture for v in conteo.values())


# ── D8: Racha de fallos → reducir volumen ────────────────────────────────────
def ajuste_volumen_por_racha(racha_fallos: int) -> dict:
    """
    D8: Si hay racha de N fallos consecutivos, reducir volumen de picks.
    Racha 3-4: reducir MAX_PICKS a la mitad.
    Racha 5+: solo picks score ≥9.0 (modo ultra-conservador).
    """
    if racha_fallos >= 5:
        return {
            "max_picks_ajustado": 2,
            "score_minimo_ajustado": 9.0,
            "motivo": f"D8: Racha de {racha_fallos} fallos — modo ultra-conservador activado",
        }
    elif racha_fallos >= 3:
        return {
            "max_picks_ajustado": 2,
            "score_minimo_ajustado": 8.5,
            "motivo": f"D8: Racha de {racha_fallos} fallos — reduciendo volumen",
        }
    return {"max_picks_ajustado": None, "score_minimo_ajustado": None, "motivo": ""}


# ── W6/W7: Fatiga y descanso Mundial ─────────────────────────────────────────
def ajuste_fatiga_mundial(dias_descanso_home: int, dias_descanso_away: int,
                           jornada: int) -> dict:
    """
    W6/W7: Ajuste de fatiga según días de descanso entre partidos en el Mundial.
    El calendario del Mundial es muy comprimido (partidos cada 3-4 días).
    Menos descanso = mayor fatiga = menor xG esperado.
    """
    penalizacion = 0.0
    motivos = []
    if dias_descanso_home <= 3:
        penalizacion -= 0.1
        motivos.append(f"Local solo {dias_descanso_home} días descanso — fatiga")
    if dias_descanso_away <= 3:
        penalizacion += 0.05  # visitante cansado = ligera ventaja local
        motivos.append(f"Visitante solo {dias_descanso_away} días descanso")
    if jornada >= 4 and (dias_descanso_home <= 4 or dias_descanso_away <= 4):
        penalizacion -= 0.05
        motivos.append(f"Fase {jornada} con poco descanso — acumulación fatiga")
    return {"ajuste_score": round(penalizacion, 2), "motivos": motivos}


# ── W11: Rotaciones detectadas J3 ────────────────────────────────────────────
def detectar_rotaciones_j3(bajas_confirmadas: int, es_j3: bool,
                            ya_clasificado: bool) -> dict:
    """
    W11: En J3 del Mundial, los equipos ya clasificados rotan masivamente.
    Si hay ≥3 bajas confirmadas + J3 + ya clasificado → penalizar el score
    porque el XI titular no juega.
    """
    if not es_j3:
        return {"rotar": False, "ajuste_score": 0.0, "motivo": ""}
    if ya_clasificado and bajas_confirmadas >= 2:
        return {
            "rotar": True,
            "ajuste_score": -0.5,
            "motivo": f"W11: J3 + clasificado + {bajas_confirmadas} bajas — rotación masiva esperada",
        }
    elif bajas_confirmadas >= 3:
        return {
            "rotar": True,
            "ajuste_score": -0.3,
            "motivo": f"W11: J3 + {bajas_confirmadas} bajas confirmadas — posible rotación",
        }
    return {"rotar": False, "ajuste_score": 0.0, "motivo": ""}


# ── W14: xGD acumulado en el torneo ──────────────────────────────────────────
def xgd_acumulado_torneo(goles_favor_torneo: list, goles_contra_torneo: list) -> float:
    """
    W14: xGD acumulado a lo largo del torneo (no solo últimos N partidos).
    Diferencia de rendimiento real en el torneo específico.
    Equipos que dominan su xGD en el torneo actual son más confiables que su
    forma de liga previa (diferente contexto competitivo).
    """
    gf = sum(goles_favor_torneo or [])
    gc = sum(goles_contra_torneo or [])
    return round(gf - gc, 1)


# ── D2: Confluencia mínima 4/5 para DC ───────────────────────────────────────
def validar_confluencia_dc(señales_positivas: int, total_señales: int = 5) -> bool:
    """
    D2: Para emitir un pick de DC se necesitan al menos 4/5 señales convergentes.
    Señales: forma reciente, solidez defensiva, H2H, xG, cuota con valor.
    Más estricto que O/U porque el DC tiene menor EV por ser de cuota más baja.
    """
    return señales_positivas >= 4


# ── CQ6: Veto combinadas mismo fixture ───────────────────────────────────────
def veto_combinada_mismo_fixture(picks: list) -> bool:
    """
    CQ6: Vetado poner más de 1 pick del mismo fixture en una combinada.
    Versión simplificada de D7 aplicada específicamente a mini-tickets.
    """
    fixture_ids = [p.get("fixture_id") for p in picks if p.get("fixture_id")]
    return len(fixture_ids) != len(set(fixture_ids))


def ajuste_correlacion_ticket(picks_ticket: list) -> float:
    """
    P2/P8: Penalizar tickets donde los legs tienen correlacion positiva
    (ambos dependen del mismo partido o mismo mercado correlacionado).
    Bonus para tickets con legs de partidos totalmente independientes.

    picks_ticket: lista de dicts con "fixture_id" y "jugada"
    Retorna: ajuste al score compuesto (positivo = menos correlacion = mejor)
    """
    if not picks_ticket or len(picks_ticket) < 2:
        return 0.0
    # Contar fixture_ids repetidos (mismos partidos en el mismo ticket)
    fixture_ids = [p.get("fixture_id") for p in picks_ticket]
    repetidos = len(fixture_ids) - len(set(fixture_ids))
    # Detectar correlaciones negativas DC+Under (las buenas para tickets)
    tiene_dc = any("doble oportunidad" in p.get("jugada","").lower() or "1x" in p.get("jugada","").lower() for p in picks_ticket)
    tiene_under = any("under" in p.get("jugada","").lower() for p in picks_ticket)
    bonus_correlacion_negativa = 0.2 if tiene_dc and tiene_under else 0.0
    penalizacion_mismo_partido = -0.3 * repetidos
    return round(bonus_correlacion_negativa + penalizacion_mismo_partido, 2)


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 16 — MINI-TICKET: PROB MÍNIMA DINÁMICA
# ─────────────────────────────────────────────────────────────────────────────

def prob_min_dinamica_mini_ticket(cuota: float) -> float:
    """
    CQ1 revisado: Probabilidad mínima dinámica para eslabones de mini-ticket.
    Formula: max(60, 103/cuota) — escala con la cuota.
    A mayor cuota, se exige mayor probabilidad para que el EV sea positivo.
    """
    return max(60.0, 103.0 / max(cuota, 1.01))

def valida_eslabon_mini_ticket(cuota: float, prob: float) -> dict:
    """
    Valida un eslabón de mini-ticket con los nuevos criterios.
    Retorna: {"valido": bool, "prob_min": float, "motivo": str}
    """
    prob_min = prob_min_dinamica_mini_ticket(cuota)

    if cuota < MINI_TICKET_CUOTA_MIN:
        return {"valido": False, "prob_min": prob_min,
                "motivo": f"Cuota {cuota} < mínima {MINI_TICKET_CUOTA_MIN}"}

    if cuota > MINI_TICKET_CUOTA_MAX:
        return {"valido": False, "prob_min": prob_min,
                "motivo": f"Cuota {cuota} > máxima {MINI_TICKET_CUOTA_MAX}"}

    if prob < prob_min:
        return {"valido": False, "prob_min": prob_min,
                "motivo": f"Prob {prob:.1f}% < mínima requerida {prob_min:.1f}% para cuota {cuota}"}

    return {"valido": True, "prob_min": prob_min,
            "motivo": f"✅ Cuota {cuota}, prob {prob:.1f}% ≥ {prob_min:.1f}%"}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 17 — B1 FIX: VALIDACIÓN DE CUOTA REAL ANTES DE EMITIR PICK
# ─────────────────────────────────────────────────────────────────────────────

def validar_cuota_real_vs_teorica(cuota_teorica: float, cuota_real: float,
                                   jugada: str) -> dict:
    """
    B1: El bot usa cuota teórica inflada. Esta función verifica que la cuota
    real de Pinnacle sea suficiente antes de emitir el pick.

    Si cuota_real < cuota_teorica × 0.90 → el pick tiene valor aparente pero
    no real. Descartar.
    """
    if not cuota_real or cuota_real <= 1.0:
        return {"valido": False,
                "motivo": "❌ B1: No se pudo obtener cuota real de Pinnacle — pick descartado"}

    ratio = cuota_real / cuota_teorica
    if ratio < 0.90:
        return {
            "valido": False,
            "motivo": f"❌ B1: Cuota real Pinnacle {cuota_real} es {(1-ratio)*100:.0f}% "
                      f"menor que la teórica {cuota_teorica} — el valor es ilusorio"
        }

    return {"valido": True,
            "motivo": f"✅ B1: Cuota real {cuota_real} vs teórica {cuota_teorica} — valor confirmado"}


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 18 — B2 FIX: VETO POR DISCREPANCIA MODELO vs PINNACLE
# ─────────────────────────────────────────────────────────────────────────────

def veto_discrepancia_modelo_pinnacle(prob_modelo: float,
                                       prob_pinnacle: float,
                                       jugada: str) -> dict:
    """
    B2: Cuando |prob_modelo - prob_pinnacle| > 15pp → veto automático.
    El mercado tiene información que el modelo no tiene.

    Si la diferencia es > 30pp → log especial (algo muy fuera de lo normal).

    Retorna: {"vetar": bool, "diff": float, "nivel": str, "motivo": str}
    """
    diff = abs(prob_modelo - prob_pinnacle)

    if diff > 30:
        return {
            "vetar": True,
            "diff": round(diff, 1),
            "nivel": "critico",
            "motivo": f"🚨 B2 CRÍTICO: Discrepancia {diff:.0f}pp modelo vs Pinnacle — "
                      f"posible error en modelo o información de mercado muy diferente"
        }

    if diff > 15:
        return {
            "vetar": True,
            "diff": round(diff, 1),
            "nivel": "alto",
            "motivo": f"❌ B2: Discrepancia {diff:.0f}pp modelo ({prob_modelo:.0f}%) vs "
                      f"Pinnacle ({prob_pinnacle:.0f}%) — pick vetado"
        }

    return {
        "vetar": False,
        "diff": round(diff, 1),
        "nivel": "normal",
        "motivo": f"✅ B2: Discrepancia {diff:.0f}pp — dentro del rango aceptable"
    }


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 19 — FUNCIÓN MAESTRA DE AJUSTE DE SCORE
# Integra todos los ajustes de las secciones anteriores en un solo call.
# ─────────────────────────────────────────────────────────────────────────────

def aplicar_todos_los_ajustes(
    score_base: float,
    jugada: str,
    liga: str,
    # Eficiencia ofensiva
    eficiencia_home: float = 1.0,
    eficiencia_away: float = 1.0,
    # xPTS gap
    xpts_gap_home: float = 0.0,
    xpts_gap_away: float = 0.0,
    # Mundial
    sede_mundial: str = "",
    home_name: str = "",
    away_name: str = "",
    jornada_torneo: int = 1,
    # Vetos
    cuota_dc: float = None,
    prob_empate: float = None,
    # Shots concedidos
    shots_conc_home: float = 5.0,
    shots_conc_away: float = 5.0,
) -> dict:
    """
    Función maestra que aplica todos los ajustes de score de V15.
    Retorna: {"score_final": float, "ajustes": list, "vetos": list}
    """
    ajuste_total = 0.0
    ajustes = []
    vetos = []

    # 1. Eficiencia de mercado por liga
    aj_liga = get_ajuste_score_eficiencia(liga)
    if aj_liga != 0:
        ajuste_total += aj_liga
        ajustes.append(f"Liga {liga} eficiencia: {aj_liga:+.2f}")

    # 2. Eficiencia ofensiva (regresión a la media)
    aj_eficiencia = ajuste_score_eficiencia_ofensiva(eficiencia_home, eficiencia_away, jugada)
    if aj_eficiencia != 0:
        ajuste_total += aj_eficiencia
        ajustes.append(f"Eficiencia ofensiva: {aj_eficiencia:+.2f}")

    # 3. xPTS gap (underperforming/overperforming)
    aj_xpts_home = ajuste_score_xpts_gap(xpts_gap_home)
    aj_xpts_away = ajuste_score_xpts_gap(-xpts_gap_away)  # invertido para visitante
    aj_xpts = (aj_xpts_home + aj_xpts_away) / 2
    if aj_xpts != 0:
        ajuste_total += aj_xpts
        ajustes.append(f"xPTS gap: {aj_xpts:+.2f}")

    # 4. Ajuste calor Mundial (solo si hay sede)
    if sede_mundial:
        calor = ajuste_xg_calor_mundial(sede_mundial, home_name, away_name, jornada_torneo)
        if calor["ajuste_score"] != 0:
            ajuste_total += calor["ajuste_score"]
            ajustes.append(f"Calor {sede_mundial}: {calor['ajuste_score']:+.2f}")

    # 5. Veto DC cuota baja
    if cuota_dc is not None and veto_dc_cuota_baja(cuota_dc):
        vetos.append(f"DC vetado: cuota {cuota_dc} < 1.25")

    if prob_empate is not None and veto_dc_prob_empate_baja(prob_empate):
        vetos.append(f"DC vetado: prob empate {prob_empate:.0%} < 18%")

    # 6. Veto victoria visitante
    if veto_victoria_visitante(jugada, liga):
        vetos.append(f"Victoria visitante vetada en {liga} (EV estructuralmente negativo)")

    # 7. Shots concedidos (proxy pressing)
    avg_shots = (shots_conc_home + shots_conc_away) / 2
    j = jugada.lower()
    if "over" in j and "2.5" in j:
        if avg_shots < 4:
            ajuste_total -= 0.3
            ajustes.append("Defensas compactas (shots<4): -0.30")
        elif avg_shots > 6:
            ajuste_total += 0.3
            ajustes.append("Defensas porosas (shots>6): +0.30")

    score_final = round(min(10.0, max(0.0, score_base + ajuste_total)), 1)

    return {
        "score_final": score_final,
        "score_base": score_base,
        "ajuste_total": round(ajuste_total, 2),
        "ajustes": ajustes,
        "vetos": vetos,
        "hay_veto": len(vetos) > 0,
    }


# ─────────────────────────────────────────────────────────────────────────────
# SECCIÓN 20 — CALIBRACIÓN CON DATOS PROPIOS (aprendizaje.json)
# ─────────────────────────────────────────────────────────────────────────────

def calibrar_por_mercado(datos_aprendizaje: list) -> dict:
    """
    Analiza aprendizaje.json para detectar sesgos de calibración por mercado.
    Retorna tabla de corrección: si el modelo declara X% pero acierta Y%, aplica corrección.

    Uso: llamar periódicamente (ej: semana a semana) y usar los factores de corrección
    para ajustar las probabilidades declaradas del modelo.
    """
    from collections import defaultdict

    # Agrupar por mercado + rango de probabilidad declarada
    grupos = defaultdict(lambda: {"aciertos": 0, "total": 0, "prob_sum": 0.0})

    for entrada in datos_aprendizaje:
        resultado = entrada.get("resultado", "")
        if resultado not in ("acierto", "fallo", "win", "loss", "W", "L"):
            continue
        mercado = entrada.get("mercado", "Desconocido")
        prob = float(entrada.get("probabilidad", 0) or 0)
        # Bucket de probabilidad en grupos de 5%
        bucket = int(prob // 5) * 5
        clave = f"{mercado}|{bucket}-{bucket+5}%"

        es_acierto = resultado.lower() in ("acierto", "win", "w")
        grupos[clave]["total"] += 1
        grupos[clave]["prob_sum"] += prob
        if es_acierto:
            grupos[clave]["aciertos"] += 1

    calibracion = {}
    for clave, stats in grupos.items():
        n = stats["total"]
        if n < 8:  # mínimo 8 picks para calibrar
            continue
        tasa_real = stats["aciertos"] / n
        prob_declarada_avg = stats["prob_sum"] / n
        sesgo = tasa_real - (prob_declarada_avg / 100)
        calibracion[clave] = {
            "n_picks": n,
            "prob_declarada_avg": round(prob_declarada_avg, 1),
            "tasa_real": round(tasa_real * 100, 1),
            "sesgo_pct": round(sesgo * 100, 1),
            "sobreconfianza": sesgo < -0.05,  # modelo dice 70%, acierta 60%
            "infraconfianza": sesgo > 0.05,   # modelo dice 60%, acierta 70%
        }

    # Resumen de mercados con mayor sesgo
    sesgos_criticos = {k: v for k, v in calibracion.items()
                       if abs(v["sesgo_pct"]) > 10 and v["n_picks"] >= 10}

    return {
        "calibracion_detallada": calibracion,
        "sesgos_criticos": sesgos_criticos,
        "total_picks_analizados": sum(v["n_picks"] for v in calibracion.values()),
    }


# ─────────────────────────────────────────────────────────────────────────────
# INSTRUCCIONES DE INTEGRACIÓN AL BOT
# ─────────────────────────────────────────────────────────────────────────────
"""
## PASO 1: Import al inicio de bot.py (después de todos los imports):
    from harrynine_mejoras_v15 import *

## PASO 2: Reemplazar constantes en bot.py (buscar y reemplazar):

    # Línea ~6381:
    MINI_TICKET_CUOTA_MIN = 1.19          # era 1.10
    MINI_TICKET_CUOTA_OBJ_MIN = 1.80      # era 1.40
    MINI_TICKET_CUOTA_OBJ_MAX = 2.50      # era 2.20
    MINI_TICKET_MAX_DIA = 3               # era 5

    # Línea ~157:
    COMB_SCORE_MIN = 8.0                  # era 7.5
    COMB_SCORE_MIN_OVER15 = 8.5           # era 8.0

    # Línea ~162:
    MAX_PICKS_DIA = 4                     # era 8

    # Línea ~168-172: SCORE_MIN_POR_CUOTA reemplazar por SCORE_MIN_POR_CUOTA_V15

## PASO 3: En obtener_recomendaciones(), al final antes del sort, añadir:
    # Veto victoria visitante
    recomendaciones = [r for r in recomendaciones
                       if not veto_victoria_visitante(r["jugada"], liga)]

## PASO 4: En _registrar_aprendizaje(), antes de agregar_json():
    # CLV tracking
    if pick.get("cuota_cierre"):
        entrada = enriquecer_aprendizaje_clv(entrada, pick["cuota_cierre"])

## PASO 5: En calcular_corners_avanzado(), reemplazar la lógica de score por:
    resultado_corners = calcular_corners_v15(
        home_corners_prom=home_estilo["corners_prom"],
        away_corners_prom=away_estilo["corners_prom"],
        home_corners_contra=home_estilo.get("corners_contra", 4.5),
        away_corners_contra=away_estilo.get("corners_contra", 4.5),
        liga=liga,
        home_name=home_name,
        away_name=away_name,
        es_mundial="world cup" in liga.lower() or "mundial" in liga.lower(),
    )

## PASO 6: En generar_picks_selecciones() o equivalente, después de calcular el score:
    ajustes = aplicar_todos_los_ajustes(
        score_base=score_final,
        jugada=jugada,
        liga=league_name,
        eficiencia_home=eficiencia_home,
        eficiencia_away=eficiencia_away,
        sede_mundial=sede,
        home_name=home,
        away_name=away,
        jornada_torneo=jornada,
    )
    score_final = ajustes["score_final"]
    if ajustes["hay_veto"]:
        continue  # skip este pick

## PASO 7: En _analizar_fixture_async(), para el AH, usar:
    linea_ah = recomendar_linea_ah(xg_home, xg_away, eficiencia_home)
    # Presentar la línea recomendada al usuario junto con la ofertada

## PASO 8 (comando /calibrar — nuevo comando admin):
    datos = leer_json(APRENDIZAJE_FILE)
    reporte = calibrar_por_mercado(datos)
    clv_reporte = analizar_clv_historico(datos)
    # Presentar resultados al admin

## PASO 9: Stake con 3 niveles — en comando /picks, al calcular stake:
    stake_info = calcular_stake_v15(
        score=rec["score"],
        prob=rec["prob"],
        cuota=cuota_real,
        bank=bank_actual,
    )
    # Mostrar stake_info["descripcion"] y stake_info["stake"]
"""


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
REFEREE_FILE = _tmp_path("arbitros_historial.json")   # V16: referee strictness
HALFTIME_FILE = _tmp_path("halftime_historial.json")  # V16: first-half scoring rate
# Suscriptores a alertas live. Un solo job global atiende a todos: asi el
# consumo de API es constante con 1 o con 30 usuarios suscritos.
ALERTAS_SUBS_FILE = _tmp_path("alertas_suscriptores.json")
# Chat IDs que reciben alarmas de combinadas — persistidos para sobrevivir reinicios
CHAT_IDS_ALARMAS_FILE = _tmp_path("chat_ids_alarmas.json")

CACHE = {}
CACHE_TTL = 600   # 10 min — reducir peticiones al API (plan free tiene límite)
CACHE_MAX_SIZE = 500   # maximo de entradas; purga las mas viejas al superarlo
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

# ── SELECCIONES NACIONALES Y MUNDIAL ────────────────────────────────────
# Incluidas en analizar_all y generar_top con motor analizar_seleccion.
# El Mundial 2026 arranca el 11 de junio (league=1, season=2026).
# ID=10: Friendlies internacionales de selecciones mayores (Portugal vs Chile, etc.)
# ID=667: Friendlies de clubes (NO de selecciones — excluido)
SELECCIONES_LEAGUES = {
    "FIFA World Cup 2026":            {"id": 1,   "season": 2026, "country": "World"},
    "Friendlies Internacionales":     {"id": 10,  "season": 2026, "country": "World"},
    "Friendlies Women":               {"id": 666, "season": 2026, "country": "World"},
    "WC Qualif. CONMEBOL":            {"id": 35,  "season": 2026, "country": "World"},
    "WC Qualif. UEFA":                {"id": 32,  "season": 2026, "country": "World"},
    "WC Qualif. CONCACAF":            {"id": 30,  "season": 2026, "country": "World"},
    "WC Qualif. AFC":                 {"id": 36,  "season": 2026, "country": "World"},
    "WC Qualif. CAF":                 {"id": 29,  "season": 2026, "country": "World"},
    "UEFA U19 Championship Qual":     {"id": 893, "season": 2026, "country": "World"},
    "Baltic Cup":                     {"id": 849, "season": 2026, "country": "World"},
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
COMB_SCORE_MIN = 8.0           # V15: era 7.5 — selectividad radical
# Over 1.5 es el eslabon que mas rompe combinadas (0-0 / 1-0). Se le exige
# un score recalibrado mas alto que al resto.
COMB_SCORE_MIN_OVER15 = 8.5   # V15: era 8.0

# ── MODO CONSERVADOR V15 ───────────────────────────────────────────────
# Maximo de picks diarios — reducido para selectividad radical (+6-10% win rate).
MAX_PICKS_DIA = 4              # V15: era 8
# Mercados permitidos en modo conservador.
MERCADOS_CONSERVADOR = {"Goles totales", "Doble oportunidad"}
# Score minimo dinamico segun cuota: mas cuota exige mas conviccion.
# V15: umbrales subidos para filtrar picks débiles.
SCORE_MIN_POR_CUOTA = [
    (1.50, 2.20, 8.0),   # V15: era 7.5 — cuota 1.50-2.20 -> score >= 8.0
    (2.21, 3.00, 8.5),   # V15: era 8.0 — cuota 2.21-3.00 -> score >= 8.5
    (3.01, 99.0, 9.0),   # V15: era 8.5 — cuota 3.01+     -> score >= 9.0
]
# Freno de bank: si el bank cae por debajo de este % del inicial, no se generan picks.
BANK_FRENO_PCT = 0.35   # 35% -> S/175 sobre S/500 inicial
# Racha de fallos consecutivos que dispara alerta.
RACHA_FALLOS_ALERTA = 5

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
    # V14.3: Mundial — modelo de selecciones más fiable en mercados de goles
    "FIFA World Cup 2026": 1.02,
    "FIFA World Cup": 1.02,
    "World Cup": 1.02,
}


def recalibrar_probabilidad(prob):
    """
    Corrige la probabilidad declarada hacia la efectividad real medida.
    Tabla corregida V14.2: monotonica (a mayor prob declarada -> mayor recalibrada).
    Eliminada la anomalia 70-74% -> 88% que promovia picks debiles.
    """
    try:
        prob = float(prob)
    except (ValueError, TypeError):
        return prob
    if prob >= 90:
        return 88.0
    if prob >= 85:
        return 84.0
    if prob >= 80:
        return 78.0
    if prob >= 75:
        return 72.0
    if prob >= 70:
        return 66.0
    return prob


def recalibrar_score(score):
    """
    Re-mapea el score a la efectividad real.
    Tabla corregida V14.2: monotonica (a mayor score -> mayor recalibrado).
    Eliminada la anomalia 7.0-7.4 -> 8.5 que promovia picks con score bajo.
    """
    try:
        score = float(score)
    except (ValueError, TypeError):
        return score
    if score >= 9.5:
        return 9.5
    if score >= 9.0:
        return 8.5
    if score >= 8.5:
        return 8.0
    if score >= 8.0:
        return 7.5
    if score >= 7.5:
        return 7.0
    if score >= 7.0:
        return 6.5
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
    V14.3: incluye penalización por tipo de competición (Sub-XX, amistosos).
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
        # V14.3: penalización por competición juvenil/amistosa
        pen_comp = _penalizacion_competicion(liga)
        score_nuevo = round(score_nuevo + pen_comp, 1)
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
    Traduce umbrales de score a umbrales de probabilidad recalibrada.
    V14.2: el score vuelve a ser el criterio principal. La prob es desempate.
      score_minimo >= 9.0 -> elite  -> prob recalibrada >= 80%
      score_minimo >= 7.5 -> normal -> prob recalibrada >= 66%
    """
    try:
        s = float(score_minimo)
        if s >= 9.0:
            return 80.0
        return 66.0
    except (ValueError, TypeError):
        return 66.0


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


# Control de peticiones API - Plan Ultra: 75,000/día
# La API bloquea ráfagas de muchas peticiones simultáneas aunque tengas cuota.
# Usamos semáforo asyncio + delay en loops síncronos para evitar 429.
_API_SEMAPHORE = None       # Se inicializa como asyncio.Semaphore cuando se necesite
_API_MAX_CONCURRENT = 3     # Max 3 peticiones async simultáneas
_API_DELAY_ENTRE_LOTES = 0.5
_API_REQUEST_COUNT = 0      # Contador de peticiones síncronas
_API_LAST_RESET = 0.0       # Timestamp del último reset del contador
_API_LIMIT_POR_MINUTO = 100 # Plan Ultra: sin límite declarado, usar 100 como tope de ráfaga

def api_get(endpoint, use_cache=True, ttl=CACHE_TTL):
    global _API_REQUEST_COUNT, _API_LAST_RESET
    now = time.time()

    # Servir desde caché si está disponible y válido
    if use_cache and endpoint in CACHE:
        saved_time, saved_data = CACHE[endpoint]
        if now - saved_time < ttl:
            return saved_data

    # Rate limiting: respetar límite del plan
    elapsed = now - _API_LAST_RESET
    if elapsed >= 60:
        _API_REQUEST_COUNT = 0
        _API_LAST_RESET = time.time()
    if _API_REQUEST_COUNT >= _API_LIMIT_POR_MINUTO:
        espera = 60 - elapsed + 1
        print(f"[RATE LIMIT] Límite alcanzado — esperando {espera:.0f}s")
        time.sleep(max(1, espera))
        _API_REQUEST_COUNT = 0
        _API_LAST_RESET = time.time()

    try:
        r = requests.get(
            f"{BASE_URL}{endpoint}",
            headers=HEADERS,
            timeout=15
        )
        _API_REQUEST_COUNT += 1

        # Manejar 429 con backoff exponencial
        if r.status_code == 429:
            retry_after = int(r.headers.get("Retry-After", _API_429_BACKOFF))
            print(f"[429 TOO MANY REQUESTS] Esperando {retry_after}s — {endpoint}")
            time.sleep(retry_after)
            # Reintentar una vez
            r = requests.get(f"{BASE_URL}{endpoint}", headers=HEADERS, timeout=15)
            _API_REQUEST_COUNT += 1

        if r.status_code != 200:
            print(f"ERROR API {r.status_code}: {endpoint}")
            return []

        data = r.json().get("response", [])

        if use_cache:
            if len(CACHE) >= CACHE_MAX_SIZE:
                now2 = time.time()
                viejos = [k for k, (t, _) in CACHE.items() if now2 - t > CACHE_TTL]
                for k in viejos:
                    CACHE.pop(k, None)
                if len(CACHE) >= CACHE_MAX_SIZE:
                    ordenados = sorted(CACHE.items(), key=lambda x: x[1][0])
                    for k, _ in ordenados[:CACHE_MAX_SIZE // 2]:
                        CACHE.pop(k, None)
            CACHE[endpoint] = (time.time(), data)

        return data

    except Exception as e:
        print("ERROR REQUEST:", e)
        return []


async def _get_api_semaphore():
    """Obtiene o crea el semáforo global para limitar concurrencia de API."""
    global _API_SEMAPHORE
    if _API_SEMAPHORE is None:
        _API_SEMAPHORE = asyncio.Semaphore(_API_MAX_CONCURRENT)
    return _API_SEMAPHORE


async def api_get_async(session, endpoint, use_cache=True, ttl=CACHE_TTL):
    """Version asincrona de api_get para llamadas paralelas."""
    import aiohttp as _aiohttp
    now = time.time()

    if use_cache and endpoint in CACHE:
        saved_time, saved_data = CACHE[endpoint]
        if now - saved_time < ttl:
            return saved_data

    sem = await _get_api_semaphore()
    try:
        async with sem:
            async with session.get(
                f"{BASE_URL}{endpoint}",
                headers=HEADERS,
                timeout=_aiohttp.ClientTimeout(total=15)
            ) as r:
                if r.status == 429:
                    retry_after = int(r.headers.get("Retry-After", 30))
                    print(f"[429 ASYNC] Rate limit — esperando {retry_after}s — {endpoint}")
                    await asyncio.sleep(retry_after)
                    # Reintentar una vez
                    async with session.get(
                        f"{BASE_URL}{endpoint}",
                        headers=HEADERS,
                        timeout=_aiohttp.ClientTimeout(total=15)
                    ) as r2:
                        if r2.status != 200:
                            return []
                        data = (await r2.json()).get("response", [])
                        if use_cache:
                            CACHE[endpoint] = (time.time(), data)
                        return data
                if r.status != 200:
                    return []
                data = (await r.json()).get("response", [])
                if use_cache:
                    CACHE[endpoint] = (time.time(), data)
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
    """Escritura atomica: escribe a .tmp y luego renombra para evitar
    corrupcion si el proceso se interrumpe a mitad de escritura."""
    path_tmp = path + ".tmp"
    try:
        with open(path_tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(path_tmp, path)
    except Exception as e:
        print(f"ERROR guardar_json_lista({path}): {e}")
        try:
            os.remove(path_tmp)
        except Exception:
            pass


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
    # Si la probabilidad viene como decimal (0-1), convertir a porcentaje
    if probabilidad < 1:
        probabilidad = probabilidad * 100
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

    # TIME DECAY V14.3: partidos mas recientes pesan mas.
    # Pesos por posicion (indice 0 = mas reciente):
    # pos 0-2: peso 1.0 | pos 3-5: peso 0.7 | pos 6+: peso 0.4
    def _peso_decay(idx):
        if idx <= 2:
            return 1.0
        elif idx <= 5:
            return 0.7
        return 0.4

    jugados = 0
    gf_total = 0.0
    gc_total = 0.0
    over15 = 0.0
    over25 = 0.0
    under35 = 0.0
    btts = 0.0
    rojas_total = 0.0
    peso_total = 0.0
    forma = []
    idx_partido = 0  # indice para calcular peso (0 = mas reciente)

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
        peso = _peso_decay(idx_partido)

        jugados += 1
        peso_total += peso
        gf_total += gf * peso
        gc_total += gc * peso

        # Tarjetas rojas del equipo en este partido
        try:
            fixture_id_p = p["fixture"]["id"]
            stats = api_get(
                f"/fixtures/statistics?fixture={fixture_id_p}",
                use_cache=True, ttl=86400  # 24h cache para partidos pasados
            )
            if stats:
                for team_data in stats:
                    t_id = team_data.get("team", {}).get("id")
                    if t_id != team_id:
                        continue
                    for item in team_data.get("statistics", []):
                        if item.get("type") == "Red Cards":
                            try:
                                rojas_total += int(str(item.get("value") or 0)) * peso
                            except Exception:
                                pass
        except Exception:
            pass

        if gf > gc:
            forma.append("W")
        elif gf == gc:
            forma.append("D")
        else:
            forma.append("L")

        over15 += peso if total >= 2 else 0
        over25 += peso if total >= 3 else 0
        under35 += peso if total <= 3 else 0
        btts += peso if (gh > 0 and ga > 0) else 0

        idx_partido += 1
        if jugados == 7:
            break

    if jugados == 0 or peso_total == 0:
        return None

    return {
        "jugados": jugados,
        "gf_prom": round(gf_total / peso_total, 3),
        "gc_prom": round(gc_total / peso_total, 3),
        "total_prom": round((gf_total + gc_total) / peso_total, 3),
        "over15": round(over15 / peso_total, 3),
        "over25": round(over25 / peso_total, 3),
        "under35": round(under35 / peso_total, 3),
        "btts": round(btts / peso_total, 3),
        "forma": "".join(forma),
        "rojas_prom": round(rojas_total / peso_total, 3),
    }




import math as _math_poisson

# ── PERFIL DE GOLES POR LIGA ─────────────────────────────────────────────
PERFIL_GOLES_LIGA = {
    "Eredivisie": +0.08, "Jupiler Pro League": +0.07, "Belgian Pro League": +0.07,
    "Austrian Bundesliga": +0.07, "Bundesliga": +0.05, "2. Bundesliga": +0.05,
    "Bundesliga 2": +0.05, "Swedish Allsvenskan": +0.06, "Norwegian Eliteserien": +0.05,
    "Premier League": +0.03, "Championship": +0.03,
    "Ligue 1": -0.07, "La Liga": -0.05, "LaLiga": -0.05,
    "Primeira Liga": -0.05, "Super Lig": -0.04, "Süper Lig": -0.04,
    "Serie A": -0.03, "Friendlies": -0.05,
    "Friendlies Internacionales": -0.05,
    "World Friendlies Internacionales": -0.05,
    "J-League": -0.02, "K League 1": -0.02,
    # V14.3: Mundial — fase de grupos promedia ~2.3 goles/partido históricamente
    # Ajuste negativo similar a LaLiga (partidos cerrados, especulación táctica)
    "FIFA World Cup 2026": -0.06,
    "FIFA World Cup": -0.06,
    "World Cup": -0.06,
}

# V14.3: Factor de penalización de score para competiciones juveniles/amistosas.
# Los modelos estadísticos son menos fiables en estas competiciones porque:
# - Rotación masiva de jugadores (amistosos)
# - Menor muestra histórica (Sub-19/20/21)
# - Alta varianza en resultados (equipos en formación)
PENALIZACION_SCORE_COMPETICION = {
    # Competiciones Sub-19
    "u19": -0.8, "u-19": -0.8, "under 19": -0.8, "under-19": -0.8,
    "sub-19": -0.8, "sub19": -0.8,
    # Competiciones Sub-20
    "u20": -0.6, "u-20": -0.6, "under 20": -0.6, "under-20": -0.6,
    "sub-20": -0.6, "sub20": -0.6,
    # Competiciones Sub-21
    "u21": -0.4, "u-21": -0.4, "under 21": -0.4, "under-21": -0.4,
    "sub-21": -0.4, "sub21": -0.4,
    # Competiciones Sub-23
    "u23": -0.3, "u-23": -0.3, "under 23": -0.3, "under-23": -0.3,
    # Amistosos de clubes (menos predecibles por rotación)
    "friendly games": -0.3, "friendlies clubs": -0.3,
    "u20 friendly": -0.6, "u19 friendly": -0.8,
}


def _penalizacion_competicion(league_name):
    """
    Retorna el ajuste negativo de score según el tipo de competición.
    Penaliza partidos juveniles y amistosos donde el modelo es menos fiable.
    """
    if not league_name:
        return 0.0
    ln = league_name.lower()
    for clave, penalizacion in PENALIZACION_SCORE_COMPETICION.items():
        if clave in ln:
            return penalizacion
    return 0.0


def _ajuste_liga_goles(league):
    """Retorna el ajuste de prob de goles para una liga dada."""
    if not league:
        return 0.0
    for nombre, ajuste in PERFIL_GOLES_LIGA.items():
        if nombre.lower() in league.lower():
            return ajuste
    return 0.0


def _correccion_dixon_coles(k_home, k_away, lam_h, lam_a, rho=-0.13):
    """
    Corrección Dixon-Coles para resultados de baja puntuación.
    Ajusta la probabilidad conjunta de resultados 0-0, 1-0, 0-1 y 1-1
    que el Poisson independiente subestima sistematicamente.
    rho=-0.13 es el valor empirico tipico para futbol europeo.
    """
    try:
        if k_home == 0 and k_away == 0:
            return 1 - lam_h * lam_a * rho
        elif k_home == 1 and k_away == 0:
            return 1 + lam_a * rho
        elif k_home == 0 and k_away == 1:
            return 1 + lam_h * rho
        elif k_home == 1 and k_away == 1:
            return 1 - rho
        return 1.0
    except Exception:
        return 1.0


def _prob_poisson(k, lam):
    """Probabilidad de Poisson P(X=k) con lambda=lam."""
    try:
        return (_math_poisson.exp(-lam) * lam**k) / _math_poisson.factorial(k)
    except Exception:
        return 0.0


def _lam_partido(gf_home, gc_home, gf_away, gc_away, league=""):
    """Calcula lambdas home y away del partido via Poisson con ajuste de liga."""
    lam_h = max(0.3, (gf_home + gf_away) / 2 * 0.6 + (gc_home + gc_away) / 2 * 0.4)
    lam_a = max(0.2, (gf_away + gf_home) / 2 * 0.5 + (gc_away + gc_home) / 2 * 0.5)
    ajuste = _ajuste_liga_goles(league)
    lam_h = lam_h * (1 + ajuste)
    lam_a = lam_a * (1 + ajuste)
    return lam_h, lam_a


def prob_under35_poisson(gf_home, gc_home, gf_away, gc_away, league=""):
    """Prob de Under 3.5 goles usando Poisson con corrección Dixon-Coles."""
    try:
        lam_h, lam_a = _lam_partido(gf_home, gc_home, gf_away, gc_away, league)
        prob = 0.0
        for gh in range(7):
            for ga in range(7):
                if gh + ga > 3:
                    continue
                p_h = _prob_poisson(gh, lam_h)
                p_a = _prob_poisson(ga, lam_a)
                tau = _correccion_dixon_coles(gh, ga, lam_h, lam_a)
                prob += p_h * p_a * tau
        return round(min(95.0, max(40.0, prob * 100)), 1)
    except Exception:
        return None


def prob_over15_poisson(gf_home, gc_home, gf_away, gc_away, league=""):
    """Prob de Over 1.5 goles usando Poisson con corrección Dixon-Coles."""
    try:
        lam_h, lam_a = _lam_partido(gf_home, gc_home, gf_away, gc_away, league)
        # prob under 1.5 = P(0-0) + P(1-0) + P(0-1)
        prob_under = 0.0
        for gh in range(3):
            for ga in range(3):
                if gh + ga > 1:
                    continue
                p_h = _prob_poisson(gh, lam_h)
                p_a = _prob_poisson(ga, lam_a)
                tau = _correccion_dixon_coles(gh, ga, lam_h, lam_a)
                prob_under += p_h * p_a * tau
        prob = 1 - prob_under
        return round(min(95.0, max(40.0, prob * 100)), 1)
    except Exception:
        return None


def prob_under25_poisson(gf_home, gc_home, gf_away, gc_away, league=""):
    """Prob de Under 2.5 goles usando Poisson con corrección Dixon-Coles."""
    try:
        lam_h, lam_a = _lam_partido(gf_home, gc_home, gf_away, gc_away, league)
        prob = 0.0
        for gh in range(5):
            for ga in range(5):
                if gh + ga > 2:
                    continue
                p_h = _prob_poisson(gh, lam_h)
                p_a = _prob_poisson(ga, lam_a)
                tau = _correccion_dixon_coles(gh, ga, lam_h, lam_a)
                prob += p_h * p_a * tau
        return round(min(92.0, max(35.0, prob * 100)), 1)
    except Exception:
        return None


def _ajustar_prob_correlacion_mismo_partido(jugada1, jugada2, prob_conjunta_pct):
    """
    Ajusta la prob conjunta cuando dos mercados son del mismo partido.
    La multiplicacion simple sobreestima porque los eventos no son independientes.
    """
    j1 = jugada1.lower()
    j2 = jugada2.lower()
    p = prob_conjunta_pct
    if (("under 3.5" in j1 and "over 1.5" in j2) or
            ("over 1.5" in j1 and "under 3.5" in j2)):
        p = p * 0.92
    elif (("under 3.5" in j1 and "over 2.5" in j2) or
            ("over 2.5" in j1 and "under 3.5" in j2)):
        p = p * 0.80
    elif (("1x" in j1 or "x2" in j1) and "under" in j2):
        p = p * 1.03
    elif ("under" in j1 and ("1x" in j2 or "x2" in j2)):
        p = p * 1.03
    return round(min(95.0, p), 1)

def calcular_prob_sin_roja(home_general, away_general, fase="group"):
    """
    Calcula la probabilidad de que el partido termine Sin Tarjeta Roja.
    Usa el historial de rojas de ambos equipos (rojas_prom de calcular_forma).
    Base estadistica: ~83% de partidos terminan sin roja en ligas normales.
    Ajustes:
      - Equipos con historial agresivo: baja prob
      - Amistosos: sube prob (arbitros mas permisivos)
      - Fases eliminatorias: baja prob (mas tension)
    Devuelve probabilidad entre 60 y 95.
    """
    # Base estadistica general
    prob_base = 83.0

    # Ajuste por historial de rojas del local
    rojas_home = float((home_general or {}).get("rojas_prom", 0.05) or 0.05)
    rojas_away = float((away_general or {}).get("rojas_prom", 0.05) or 0.05)
    rojas_prom = (rojas_home + rojas_away) / 2.0

    # A mayor promedio de rojas, menor prob de partido limpio
    # 0 rojas/partido → +5%, 0.2 rojas/partido → -10%, 0.5+ → -20%
    if rojas_prom == 0:
        ajuste_rojas = +5.0
    elif rojas_prom <= 0.1:
        ajuste_rojas = 0.0
    elif rojas_prom <= 0.2:
        ajuste_rojas = -8.0
    elif rojas_prom <= 0.4:
        ajuste_rojas = -15.0
    else:
        ajuste_rojas = -22.0

    # Ajuste por fase del torneo
    ajuste_fase = 0.0
    if fase == "friendly":
        ajuste_fase = +5.0   # arbitros mas permisivos en amistosos
    elif fase in ("semi", "final"):
        ajuste_fase = -8.0   # maxima tension
    elif fase in ("quarter", "round_of_16"):
        ajuste_fase = -5.0   # tension eliminatoria

    prob_final = prob_base + ajuste_rojas + ajuste_fase
    return round(max(60.0, min(95.0, prob_final)), 1)


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


def obtener_recomendaciones(home_general, away_general, home_home, away_away, liga="", eficiencia_home=1.0, eficiencia_away=1.0, xpts_gap_home=0.0, xpts_gap_away=0.0, shots_conc_home=5.0, shots_conc_away=5.0):
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

    # N8: Under 2.5 baseline grupos Mundial ~55%
    if liga and any(x in liga.lower() for x in ["world cup", "mundial", "fifa"]):
        _n8_bonus = ajuste_under25_grupos_mundial(True, "group", under25 * 100 if under25 <= 1 else under25)
        score_under += _n8_bonus

    if score_under >= 7:
        prob = min(91, 66 + score_under * 2)
        # V15 Z26-Z29: Criterios refinados Under/Over 3.5
        _eval_35 = evaluar_over35(
            xg_combinado=total_prom,
            xga_home=float(base_home.get("gc_prom", 1.0) or 1.0),
            xga_away=float(base_away.get("gc_prom", 1.0) or 1.0),
            h2h_avg_goles=total_prom,
            liga=liga,
            fase_mundial="",
        )
        if _eval_35["señal"] == "under35":
            score_under_adj = score_under + (_eval_35["score"] - 5.0) * 0.3
            add_pick(
                "Under 3.5 goles",
                prob,
                "Tendencia under fuerte, bajo promedio goleador y baja frecuencia de partidos rotos. | " + " | ".join(_eval_35["motivos"][:2]),
                score_under_adj,
            )
        elif _eval_35["señal"] == "over35":
            # Over 3.5 tiene valor — agregar como pick separado
            add_pick(
                "Over 3.5 goles",
                min(75, 50 + int(_eval_35["score"]) * 2),
                " | ".join(_eval_35["motivos"][:3]),
                _eval_35["score"],
            )
        else:
            add_pick(
                "Under 3.5 goles",
                prob,
                "Tendencia under fuerte, bajo promedio goleador y baja frecuencia de partidos rotos.",
                score_under,
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
        # V15 Z21-Z25: Evaluar si Over 1.5 es mejor que Over 2.5
        _o15_home_rate = base_home.get("over15", 0.75) * 100
        _o15_away_rate = base_away.get("over15", 0.75) * 100
        _eval_o15 = evaluar_over15_vs_over25(
            xg_combinado=total_prom,
            cuota_over15=1.35,
            cuota_over25=1.85,
            scoring_rate_home=_o15_home_rate,
            scoring_rate_away=_o15_away_rate,
            liga=liga,
        )
        score_over15 += _eval_o15["score_bonus"]
        # Z23: Goal expectancy >= 2.76 bonus adicional
        _ge_eval = evaluar_goal_expectancy_over15(total_prom, _o15_home_rate, _o15_away_rate)
        score_over15 += _ge_eval["score_bonus"]
        motivo_o15 = "Alta frecuencia de partidos con minimo 2 goles y produccion ofensiva suficiente."
        if _eval_o15["motivos"]:
            motivo_o15 += " | " + " | ".join(_eval_o15["motivos"][:2])
        if _ge_eval["motivo"]:
            motivo_o15 += " | " + _ge_eval["motivo"]
        # Z24: EPL baseline estructural
        _z24_bonus = ajuste_epl_over15(liga, over15 * 100 if over15 <= 1 else over15)
        score_over15 += _z24_bonus
        add_pick("Over 1.5 goles", min(90, 65 + score_over15 * 2), motivo_o15, score_over15)

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

    # V16: xG momentum — comparar goles/pto recientes (L5) vs promedio general
    _gf_l5_home = float(base_home.get("goles_favor_l5") or base_home.get("gf_prom") or gf_home or 0)
    _gf_l5_away = float(base_away.get("goles_favor_l5") or base_away.get("gf_prom") or gf_away or 0)
    _xg_momentum_home = _gf_l5_home - gf_home  # positivo = equipo en forma ascendente
    _xg_momentum_away = _gf_l5_away - gf_away

    # O10: Racha Under 2.5 >= 4 partidos consecutivos
    _under_racha_home = [r == "U" for r in base_home.get("under25_racha", [])]
    _under_racha_away = [r == "U" for r in base_away.get("under25_racha", [])]
    _racha_under = detectar_racha_under25(_under_racha_home, _under_racha_away)
    score_under += _racha_under["score_bonus"]
    motivo_under_extra = _racha_under["motivo"] if _racha_under["motivo"] else ""

    # V16: Usar forma_tabla (standings) si disponible
    _forma_tabla_home = base_home.get("forma_tabla", "")
    _forma_tabla_away = base_away.get("forma_tabla", "")
    if _forma_tabla_home and len(_forma_tabla_home) >= 3:
        _wins_from_tabla = _forma_tabla_home.count("W")
        if _wins_from_tabla >= 4:
            score_over25 = (score_over25 if "score_over25" in dir() else 0) + 0.3
        elif _wins_from_tabla <= 1:
            score_under = (score_under if "score_under" in dir() else 0) + 0.2

    # V16: Usar goal_diff de standings como señal adicional
    _gdiff_home = base_home.get("goal_diff", 0) or 0
    _gdiff_away = base_away.get("goal_diff", 0) or 0
    if _gdiff_home > 10 and _gdiff_away < -5:
        score_over25 = (score_over25 if "score_over25" in dir() else 0) + 0.4  # mismatch claro
    elif _gdiff_home < -5 and _gdiff_away < -5:
        score_under = (score_under if "score_under" in dir() else 0) + 0.3  # ambos defensivos

    # V17: GAP rating ajuste directo al score
    _gap_total = _ou25_result.get("gap_total", 0)
    if _gap_total > 3.0:
        score_over25 = (score_over25 if "score_over25" in dir() else 0) + 0.3
    elif _gap_total < 1.5 and _gap_total > 0:
        score_under = (score_under if "score_under" in dir() else 0) + 0.2

    # V17: xG corners (CK1) — añadir al total_prom
    _ck1 = calcular_xg_corners(
        float(base_home.get("corners_prom",5)),
        float(base_away.get("corners_prom",5))
    )
    _total_prom_con_corners = total_prom + _ck1["xg_total"]

    # V16: xG momentum bonus
    if "_xg_momentum_home" in dir() and "_xg_momentum_away" in dir():
        _momentum_total = _xg_momentum_home + _xg_momentum_away
        if _momentum_total > 0.8:
            score_over25 = (score_over25 if "score_over25" in dir() else 0) + 0.3
        elif _momentum_total < -0.8:
            score_under = (score_under if "score_under" in dir() else 0) + 0.3

    # Z2: Ambos marcaron últimos 5 → confirmador Over 2.5
    _scored_home_pct = base_home.get("scored_pct", 0.7) * 100
    _scored_away_pct = base_away.get("scored_pct", 0.7) * 100
    _z2 = confirmar_btts_ambos_marcaron(_scored_home_pct, _scored_away_pct)
    score_over25 = score_over25 if "score_over25" in dir() else 0
    score_over25 += _z2["score_bonus"]

    # O1: Umbral Over 2.5 dinámico por liga
    _umbral_over25_liga = umbral_over25_dinamico(liga, "over") / 100  # convertir a decimal

    # V17: Aplicar ajustes del sistema especializado OU25 al score
    _ou25_pick = _ou25_result.get("pick","over25")
    _ou25_score = _ou25_result.get("score", 0.0)
    _ou25_señales = _ou25_result.get("señales", [])
    if _ou25_result.get("recomendar"):
        if _ou25_pick == "over25":
            score_over25 = (score_over25 if "score_over25" in dir() else 0)
            score_over25 = round(score_over25 + (_ou25_score - 5.0) * 0.3, 1)
        else:
            score_under = (score_under if "score_under" in dir() else 0)
            score_under = round(score_under + (_ou25_score - 5.0) * 0.3, 1)

    # V16: Usar scoring_rate_l5 de /predictions si disponible (más preciso)
    def _pct_str(s, default=50.0):
        try: return float(str(s or default).replace("%",""))
        except: return default

    _sr_home_l5 = _pct_str(base_home.get("scoring_rate_l5")) / 100
    _sr_away_l5 = _pct_str(base_away.get("scoring_rate_l5")) / 100
    _cs_home_l5 = _pct_str(base_home.get("clean_sheet_l5")) / 100
    _cs_away_l5 = _pct_str(base_away.get("clean_sheet_l5")) / 100

    # V15 Z1-Z6: Criterios refinados Over 2.5
    # Usar scoring_rate_l5 de predictions si >0, sino el over25 histórico
    _over25_home_pct = (_sr_home_l5 * 100) if _sr_home_l5 > 0.1 else base_home.get("over25", 0) * 100
    _over25_away_pct = (_sr_away_l5 * 100) if _sr_away_l5 > 0.1 else base_away.get("over25", 0) * 100
    _combined_pct_25 = calcular_combined_pct_over25(_over25_home_pct, _over25_away_pct)
    _failed_score_away = (1 - (base_away.get("scored_pct") or _sr_away_l5 or 0.6)) * 100
    _first_half_both = base_home.get("first_half_goals", 0.5) * 100
    _rolling3 = total_prom  # mejor aproximacion disponible
    _liga_avg_over25 = 52.0  # baseline; ajustar con PERFIL_GOLES_LIGA si disponible
    _crit_over25 = criterios_over25(
        combined_pct=_combined_pct_25,
        failed_to_score_away=_failed_score_away,
        first_half_goals_both=_first_half_both,
        rolling3_avg_goles=_rolling3,
        liga_avg_over25=_liga_avg_over25,
        shots_concedidos_home=shots_conc_home,
        shots_concedidos_away=shots_conc_away,
    )
    score_over25 += _crit_over25["score_bonus"]

    if score_over25 >= 7:
        prob = min(83, 56 + score_over25 * 2)
        motivo_over25 = "Promedio goleador alto, tendencia ofensiva y señales de partido abierto."
        if _crit_over25["motivos"]:
            motivo_over25 += " | " + " | ".join(_crit_over25["motivos"][:2])
        add_pick("Over 2.5 goles", prob, motivo_over25, score_over25)

    # BTTS (Ambos marcan) ELIMINADO de la generacion: efectividad real
    # 41.6% (101 picks). La variable `btts` se conserva mas arriba porque
    # alimenta los scores de Under y Over 2.5; solo se elimina la emision
    # del pick. BTTS tambien sigue excluido de combinadas y alertas.

    # O8/NM4/P11: BTTS-No en mismatches
    _clean_sheet_home_pct = base_home.get("clean_sheet_pct", 0) * 100
    _failed_score_away_pct = (1 - base_away.get("scored_pct", 0.6)) * 100
    _diff_ranking_recs = 0  # disponible si se pasa desde contexto superior
    _btts_no = evaluar_btts_no(_clean_sheet_home_pct, 0, _failed_score_away_pct, _diff_ranking_recs)
    if _btts_no["recomendar"]:
        add_pick(
            "BTTS-No (al menos uno no marca)",
            int(_btts_no["prob_btts_no"]),
            "Mismatch claro: " + " | ".join(_btts_no["motivos"][:2]),
            _btts_no["score"],
        )

    # V15 P10-P15: Empate directo como mercado independiente
    # Solo cuando modelo > 28% + mercado < 30% + cuota >= 3.20
    _prob_empate_modelo = round((1 - over25 * 0.7) * 30, 1)  # proxy: partidos sin Over 2.5 tienden al empate
    _prob_empate_pinnacle = _prob_empate_modelo * 0.95        # aproximacion conservadora
    _cuota_empate_est = round(1 / max(0.01, _prob_empate_modelo / 100), 2)
    if _prob_empate_modelo >= 28 and _cuota_empate_est >= 3.20:
        _eval_empate = evaluar_empate_directo(
            prob_empate_modelo=_prob_empate_modelo,
            prob_empate_pinnacle=_prob_empate_pinnacle,
            cuota_empate=_cuota_empate_est,
            h2h_empates=0,
            h2h_total=5,
            liga=liga,
        )
        if _eval_empate["recomendar"]:
            add_pick(
                "Empate",
                int(_prob_empate_modelo),
                "Empate con valor: modelo supera al mercado. | " + " | ".join(_eval_empate["motivos"][:2]),
                _eval_empate["score"],
            )

    # M3: xGD acumulado ajuste final de score
    _xgd_home = float(base_home.get("xgd", 0) or 0)
    _xgd_away = float(base_away.get("xgd", 0) or 0)

    # V17: Sistema especializado O/U 2.5 — evalúa TODAS las variables
    _ou25_result = evaluar_sistema_ou25_especializado(
        liga=liga, eq_home=home, eq_away=away,
        pos_home=int(base_home.get("posicion") or 10),
        pos_away=int(base_away.get("posicion") or 10),
        desc_home=str(base_home.get("descripcion") or ""),
        desc_away=str(base_away.get("descripcion") or ""),
        xg_home=float(base_home.get("xg_pred") or total_prom*0.55 or 1.2),
        xg_away=float(base_away.get("xg_pred") or total_prom*0.45 or 1.0),
        shots_h=float(base_home.get("shots_prom") or 0),
        shots_a=float(base_away.get("shots_prom") or 0),
        ib_h=float(base_home.get("shots_insidebox") or 0),
        ib_a=float(base_away.get("shots_insidebox") or 0),
        sot_h=float(base_home.get("sog_prom") or 0),
        sot_a=float(base_away.get("sog_prom") or 0),
        corners_h=float(base_home.get("corners_prom") or 5),
        corners_a=float(base_away.get("corners_prom") or 5),
        over25_h_casa=float(base_home.get("over25_casa") or base_home.get("over25",0.5)*100),
        over25_a_visita=float(base_away.get("over25_visita") or base_away.get("over25",0.5)*100),
        ht_rate_h=float(base_home.get("ht_scoring_rate") or 0.5),
        ht_rate_a=float(base_away.get("ht_scoring_rate") or 0.5),
        gk_saves_h=float(base_home.get("goalkeeper_saves") or 0),
        sot_rival_h=float(base_away.get("sog_prom") or 0),
        goles_rec_h=float(base_home.get("gc_prom") or 0),
        passes_acc_h=float(base_home.get("passes_accurate") or 0),
        dangerous_h=float(base_home.get("dangerous_attacks") or 0),
        passes_acc_a=float(base_away.get("passes_accurate") or 0),
        dangerous_a=float(base_away.get("dangerous_attacks") or 0),
        cuota_over25=float(base_home.get("cuota_over25") or 0),
        cuota_under25=float(base_home.get("cuota_under25") or 0),
        cuota_ap_over=float(base_home.get("cuota_apertura_over25") or 0),
        fechas_h=base_home.get("fechas_partidos") or [],
        fechas_a=base_away.get("fechas_partidos") or [],
        h2h_list=base_home.get("h2h_partidos") or [],
        temp=20.0, lluvia=0.0, viento=0.0,
        horas_antes=6.0,
        nm_h=int(base_home.get("partidos_nuevo_manager") or 99),
        nm_a=int(base_away.get("partidos_nuevo_manager") or 99),
        pts_h=int(base_home.get("puntos") or 0),
        pts_a=int(base_away.get("puntos") or 0),
        n_partidos=int(base_home.get("partidos_jugados") or 20),
    )

    # V16: Calcular ratios nuevos desde el contexto del análisis
    _ctx_v16 = {
        "home_xg_pred": total_prom * 0.55, "away_xg_pred": total_prom * 0.45,
        "home_possession": base_home.get("possession", 50),
        "away_possession": base_away.get("possession", 50),
        "home_corners_prom": base_home.get("corners_prom", 5),
        "away_corners_prom": base_away.get("corners_prom", 5),
        "home_goles_favor_prom": base_home.get("gf_prom", 0),
        "away_goles_favor_prom": base_away.get("gf_prom", 0),
        "home_shots_insidebox": base_home.get("shots_insidebox", 0),
        "away_shots_insidebox": base_away.get("shots_insidebox", 0),
        "home_shots_total": base_home.get("shots_prom", 0),
        "away_shots_total": base_away.get("shots_prom", 0),
        "home_fouls": base_home.get("fouls", 0),
        "away_fouls": base_away.get("fouls", 0),
        "home_ht_scoring_rate": base_home.get("ht_scoring_rate", 0.5),
        "away_ht_scoring_rate": base_away.get("ht_scoring_rate", 0.5),
        "api_under_over": base_home.get("api_under_over", ""),
        "api_cmp_att_home": base_home.get("cmp_att", "50%"),
        "api_cmp_att_away": base_away.get("cmp_att", "50%"),
        "api_cmp_def_home": base_home.get("cmp_def", "50%"),
        "api_cmp_def_away": base_away.get("cmp_def", "50%"),
        "api_cmp_form_home": base_home.get("cmp_form", "50%"),
        "api_cmp_form_away": base_away.get("cmp_form", "50%"),
        "home_posicion": base_home.get("posicion", 10),
        "away_posicion": base_away.get("posicion", 10),
        "home_goles_favor_casa": base_home.get("gf_casa", 0),
        "home_goles_contra_casa": base_home.get("gc_casa", 0),
        "home_played_casa": base_home.get("played_casa", 1),
        "away_goles_favor_visita": base_away.get("gf_visita", 0),
        "away_goles_contra_visita": base_away.get("gc_visita", 0),
        "away_played_visita": base_away.get("played_visita", 1),
        "home_scoring_rate_l5": base_home.get("scoring_rate_l5", "50%"),
        "away_scoring_rate_l5": base_away.get("scoring_rate_l5", "50%"),
        "liga_nombre": liga,
    }
    _ratios_v16 = calcular_ratios_v16(_ctx_v16)
    _arbitro_perfil = get_referee_strictness(base_home.get("arbitro", ""))

    # ── V15: Aplicar ajustes de score y vetos ────────────────────────────
    recomendaciones_filtradas = []
    for rec in recomendaciones:
        jugada = rec["jugada"]
        # M3: Ajuste xGD por jugada
        _xgd_adj = ajuste_score_xgd(_xgd_home, _xgd_away, jugada)
        rec["score"] = round(min(10.0, rec["score"] + _xgd_adj), 1)
        # V16: Aplicar ajustes de ratios nuevos
        _adj_v16 = ajuste_score_v16(rec["score"], _ratios_v16, jugada, _arbitro_perfil)
        rec["score"] = _adj_v16["score_final"]
        if _adj_v16["ajustes"]:
            rec["v16_ajustes"] = _adj_v16["ajustes"]
        # B: Veto victoria visitante en ligas top (EV negativo estructural)
        if veto_victoria_visitante(jugada, liga):
            continue
        # B: Veto Over 3.5 en ligas defensivas
        if "over 3.5" in jugada.lower() and veto_over35_liga(liga):
            continue
        # Aplicar todos los ajustes de score V15
        resultado_ajuste = aplicar_todos_los_ajustes(
            score_base=rec["score"],
            jugada=jugada,
            liga=liga,
            eficiencia_home=eficiencia_home,
            eficiencia_away=eficiencia_away,
            xpts_gap_home=xpts_gap_home,
            xpts_gap_away=xpts_gap_away,
            shots_conc_home=shots_conc_home,
            shots_conc_away=shots_conc_away,
        )
        if resultado_ajuste["hay_veto"]:
            continue
        rec["score"] = resultado_ajuste["score_final"]
        rec["v15_ajustes"] = resultado_ajuste["ajustes"]
        recomendaciones_filtradas.append(rec)

    recomendaciones_filtradas.sort(key=lambda x: (x["score"], x["prob"]), reverse=True)
    return recomendaciones_filtradas


def _prob_empate_desde_cuotas(cuotas_1x2):
    """
    V14.3: Calcula la probabilidad implícita de empate desde las cuotas 1X2
    de Pinnacle, quitando el margen (vig) para obtener la prob real.
    Retorna float entre 0 y 1, o None si no hay datos.
    Usado para filtrar picks de DC cuando la prob de empate es baja.
    """
    try:
        if not cuotas_1x2 or "Draw" not in cuotas_1x2:
            return None
        # Quitar margen: suma de probs implícitas > 1
        p_home = 1 / cuotas_1x2["Home"] if "Home" in cuotas_1x2 else 0
        p_draw = 1 / cuotas_1x2["Draw"]
        p_away = 1 / cuotas_1x2["Away"] if "Away" in cuotas_1x2 else 0
        total = p_home + p_draw + p_away
        if total <= 0:
            return None
        # Prob de empate sin margen
        return round(p_draw / total, 3)
    except Exception:
        return None


def calcular_stake_kelly(prob_decimal, cuota, bank, fraccion=0.25):
    """
    V14.3: Calcula el stake óptimo usando Kelly fraccionado (25% por defecto).
    Kelly = (prob * cuota - 1) / (cuota - 1)
    Si Kelly es negativo, el pick no tiene value → stake = 0.
    Retorna el stake recomendado en soles y el Kelly% como referencia.
    fraccion=0.25 es conservador — reduce volatilidad y riesgo de ruina.
    """
    try:
        prob = float(prob_decimal)
        cuota = float(cuota)
        bank = float(bank)
        if cuota <= 1.0 or prob <= 0 or prob >= 1:
            return 0, 0
        kelly_pct = (prob * cuota - 1) / (cuota - 1)
        if kelly_pct <= 0:
            return 0, round(kelly_pct * 100, 1)
        kelly_fraccionado = kelly_pct * fraccion
        stake = round(bank * kelly_fraccionado, 2)
        return max(0, stake), round(kelly_pct * 100, 1)
    except Exception:
        return 0, 0


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
                movimiento = f"subio {cambio}"
            elif cambio < 0:
                movimiento = f"bajo {abs(cambio)}"
            else:
                movimiento = "sin cambio"
            # V15 X11-X12: Analizar si el movimiento es sospechoso
            _ts_anterior = previos[-1].get("fecha", "")
            try:
                _hace_2h = cuota_anterior  # usamos cuota anterior como proxy "hace 2h"
                _analisis_mov = analizar_movimiento_cuota(
                    cuota_hace_2h=_hace_2h,
                    cuota_actual=cuota,
                    jugada=jugada,
                    hay_noticias=False,
                )
                if _analisis_mov["flag"] in ("posible_lesion_silenciosa", "dinero_sharp"):
                    movimiento = movimiento + " | " + _analisis_mov["accion"]
                # N10: RLM — cuota underdog baja >0.15 desde apertura
                _rlm = detectar_rlm(cuota_apertura=cuota_anterior, cuota_actual=cuota, es_favorito=False)
                if _rlm["rlm"]:
                    movimiento = (movimiento or "") + " | " + _rlm["motivo"]
            except Exception:
                pass

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
                        # Ampliar matching: "Total Corners", "Corner Kicks", "Corners", etc.
                        es_mkt_corner = (
                            "corner" in jugada_l and (
                                "corner" in bet_name.lower()
                                or "corners" in bet_name.lower()
                                or "corner kicks" in bet_name.lower()
                                or "total corners" in bet_name.lower()
                            )
                        )
                        es_mkt_tarjeta = (
                            "tarjeta" in jugada_l and (
                                "card" in bet_name.lower()
                                or "booking" in bet_name.lower()
                                or "yellow" in bet_name.lower()
                            )
                        )
                        es_mkt = es_mkt_corner or es_mkt_tarjeta
                        if linea is not None and es_mkt and tipo in nombre.lower():
                            import re as _re_l3
                            mnum3 = _re_l3.search(r"(\d+\.?\d*)", nombre)
                            if mnum3 and abs(float(mnum3.group(1)) - linea) < 0.26:
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
                # V16: Nuevos campos
                elif tipo == "Shots insidebox":
                    shots_ib = valor
                elif tipo == "Fouls":
                    fouls = valor
                elif tipo == "Goalkeeper Saves":
                    gk_saves = valor
                elif tipo == "Passes accurate":
                    passes_acc = valor
                elif tipo in ("Passes %", "Passes%"):
                    passes_pct_v = valor

            total_corners += corners
            total_cards += yellows + (reds * 2)
            total_shots += shots
            total_sog += sog
            total_ib = total_ib + shots_ib if "total_ib" in dir() else shots_ib
            total_fouls = total_fouls + fouls if "total_fouls" in dir() else fouls
            total_gk = total_gk + gk_saves if "total_gk" in dir() else gk_saves
            validos += 1

    if validos == 0:
        return None

    result = {
        "corners_prom": total_corners / validos,
        "cards_prom": total_cards / validos,
        "shots_prom": total_shots / validos,
        "sog_prom": total_sog / validos,
    }
    if "total_ib" in dir() and total_ib > 0:
        result["shots_insidebox"] = total_ib / validos
    if "total_fouls" in dir() and total_fouls > 0:
        result["fouls"] = total_fouls / validos
    if "total_gk" in dir() and total_gk > 0:
        result["goalkeeper_saves"] = total_gk / validos
    return result



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
                elif tipo in ("Passes", "Crosses", "Total passes"):
                    if tipo == "Crosses":
                        crosses_p = val
                # V16: Campos adicionales para corners
                elif tipo == "Shots insidebox":
                    shots_ib_p = val
                elif tipo == "Dangerous Attacks":
                    dangerous_p = val

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

    home_estilo = analizar_estilo_corners(home_id, last=6)   # V15: 6 en vez de 10 (más relevante)
    away_estilo = analizar_estilo_corners(away_id, last=6)

    if not home_estilo or not away_estilo:
        return recomendaciones

    # Media total de corners del partido (ambos equipos)
    corners_prom_partido = home_estilo["corners_prom"] + away_estilo["corners_prom"]

    # V15 Z16-Z20: Aplicar criterios refinados de corners
    corners_contra_home = home_estilo.get("corners_contra", 4.5)
    corners_contra_away = away_estilo.get("corners_contra", 4.5)
    liga_name = getattr(calcular_corners_avanzado, "_liga_actual", "")
    resultado_v15 = calcular_corners_v15(
        home_corners_prom=home_estilo["corners_prom"],
        away_corners_prom=away_estilo["corners_prom"],
        home_corners_contra=corners_contra_home,
        away_corners_contra=corners_contra_away,
        liga=liga_name,
        home_name=home_name,
        away_name=away_name,
    )
    # Si los criterios V15 detectan dominio asimétrico, penalizar el score
    _v15_corners_penalty = 0.0 if resultado_v15["contribucion_equitativa"] else -1.0
    _v15_corners_motivos = resultado_v15["motivos"]

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
            score = round(min(9.5, 6.0 + (corners_esperados - linea) * 0.8 + _v15_corners_penalty), 1)
            riesgo = round(max(1, 4 - (corners_esperados - linea) * 0.5), 1)
            motivo_completo = motivo
            if _v15_corners_motivos:
                motivo_completo += " | " + " | ".join(_v15_corners_motivos)
            recomendaciones.append({
                "mercado": "Corners",
                "jugada": f"Corners Over {linea}",
                "prob": round(prob, 1),
                "score": score,
                "riesgo": riesgo,
                "confianza": etiqueta_confianza(score),
                "motivo": motivo_completo,
                "cuota_minima": cuota_minima(prob/100, riesgo),
                "cuota": cuota_minima(prob/100, riesgo),
                "corners_esperados": corners_esperados,
                "home_estilo": home_estilo["estilo"],
                "away_estilo": away_estilo["estilo"],
                "v15_equitativo": resultado_v15["contribucion_equitativa"],
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

    # DC8: Veto DC en amistosos — pasar liga desde el contexto superior
    _liga_dc = ""  # se actualiza si la función recibe liga como parámetro

    if diferencia >= 3:
        # V15 Z7-Z10: Validar criterios DC antes de emitir
        _forma_visitante_ok = (base_away["forma"].count("W") + base_away["forma"].count("D")) / max(len(base_away["forma"]), 1) * 100
        _h2h_draws = 0
        _dc_val = validar_dc(
            cuota_dc_ofertada=1.50,  # cuota conservadora; se actualiza con real
            prob_empate=0.25,
            liga="",
            es_x2=False,
            forma_visitante_sin_derrota_pct=50.0,
        )
        _score_dc = 8.0 + _dc_val["score_bonus"]
        # D2: Confluencia mínima 4/5 señales para DC
        _señales_dc = sum([
            1 if home_score > 5 else 0,          # forma ofensiva
            1 if base_home.get("gc_prom", 2) < 1.2 else 0,  # solidez defensiva
            1 if diferencia >= 4 else 0,          # diferencia clara
            1 if base_home.get("over15", 0) > 0.7 else 0,   # scoring rate
            1 if _dc_val["valido"] else 0,        # cuota con valor
        ])
        if not validar_confluencia_dc(_señales_dc):
            pass  # No vetar pero bajar el score
        add_dc(
            f"1X ({home} o empate)",
            78,
            _score_dc,
            2.8,
            f"{home} muestra mejor forma reciente, mayor solidez y menor probabilidad de derrota."
        )

    elif diferencia <= -3:
        # V15 Z8: X2 — verificar forma visitante sin derrota >= 30%
        _forma_away_no_derrota = (base_away["forma"].count("W") + base_away["forma"].count("D")) / max(len(base_away["forma"]), 1) * 100
        _dc_val_x2 = validar_dc(
            cuota_dc_ofertada=1.50,
            prob_empate=0.25,
            liga="",
            es_x2=True,
            forma_visitante_sin_derrota_pct=_forma_away_no_derrota,
        )
        if _dc_val_x2["valido"]:
            _score_dc_x2 = 8.0 + _dc_val_x2["score_bonus"]
            add_dc(
                f"X2 ({away} o empate)",
                78,
                _score_dc_x2,
                2.8,
                f"{away} muestra mejor forma reciente, mayor solidez y menor probabilidad de derrota."
            )

    elif abs(diferencia) < 1.5:
        # Partido parejo: no forzamos doble oportunidad
        pass

    # DC7/P14: Away favorite bias — DC 1X del local cuando favorito visita ≤1.70
    # (se detecta en enriquecer_con_odds; aquí solo preparamos la estructura)

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
            # Edge se calcula con prob ORIGINAL (antes de recalibrar) para
            # no introducir sesgos de la tabla de recalibracion en el filtro.
            prob_para_edge = float(
                r.get("prob_original", r.get("prob", 0)) or 0
            )
            r["edge"] = edge_estimado(prob_para_edge, cuota)
            r["movimiento"] = guardar_snapshot_odds(
                fixture_id,
                r["jugada"],
                cuota
            )
            # ── V15 B1: Validar cuota real vs teórica ──────────────────
            cuota_teorica = r.get("cuota_justa") or cuota_justa(prob_para_edge)
            b1_check = validar_cuota_real_vs_teorica(cuota_teorica, cuota, r["jugada"])
            r["b1_valido"] = b1_check["valido"]
            r["b1_motivo"] = b1_check["motivo"]
            # ── V15 B2: Veto discrepancia modelo vs mercado ─────────────
            prob_pinnacle = round((1 / cuota) * 100, 1)
            b2_check = veto_discrepancia_modelo_pinnacle(prob_para_edge, prob_pinnacle, r["jugada"])
            r["b2_vetar"] = b2_check["vetar"]
            r["b2_motivo"] = b2_check["motivo"]
            # ── V16: Ensemble 3 modelos ──────────────────────────────────
            _prob_xg_api = float(r.get("xg_pred_total") or 0)
            if _prob_xg_api > 0:
                # Convertir xG a probabilidad Over 2.5 via Poisson
                import math as _math_e
                _lam = max(0.1, _prob_xg_api)
                _prob_over25_xg = round((1 - sum(
                    _math_e.exp(-_lam) * (_lam**k) / _math_e.factorial(k)
                    for k in range(3))) * 100, 1)
                _prob_ensemble = calcular_ensemble_v16(
                    prob_para_edge, _prob_over25_xg, prob_pinnacle)
                r["prob_ensemble"] = _prob_ensemble
                # Si ensemble difiere mucho del modelo solo → ajustar score
                diff_ensemble = abs(prob_para_edge - _prob_ensemble)
                if diff_ensemble > 8:
                    r["score"] = round(r["score"] * 0.92, 1)  # reducir si hay divergencia
            # ── V15c N2: De-vig Pinnacle (informativo) ────────────────
            # El resultado se guarda en el pick para referencia del usuario
            # Se necesitan las 3 cuotas 1X2, aquí solo tenemos la del pick
            r["cuota_sin_vig"] = round(cuota * 0.975, 3)  # aproximacion: ~2.5% margen

            # ── V15c O7/P1: Línea asiática recomendada zona gris ───────
            _xg_total_pick = float(r.get("xg_pred_total") or 0)
            if _xg_total_pick > 0 and "goles" in r.get("jugada", "").lower():
                _linea_asiatica = recomendar_linea_asiatica_goles(_xg_total_pick, r.get("liga", ""))
                if _linea_asiatica["ev_mejorado"]:
                    r["linea_asiatica_sugerida"] = _linea_asiatica["linea_recomendada"]

            # ── V15b P4: Veto zona peligro Mundial 1.30-1.60 ───────────
            _es_mundial_pick = any(x in r.get("liga", "").lower()
                                   for x in ["world cup", "mundial", "fifa"])
            _p4 = veto_zona_peligro_mundial(cuota, _es_mundial_pick)
            if _p4["vetar"] and "1x2" in r.get("mercado", "").lower():
                r["b2_vetar"] = True
                r["b2_motivo"] = _p4["motivo"]
            # ── V15b DC10: Sugerir DC sobre 1X2 en Mundial ─────────────
            _diff_elo_pick = r.get("diff_ranking", 0) * 3  # proxy ELO
            _dc10 = preferir_dc_sobre_1x2_mundial(cuota, cuota * 0.85,
                                                   int(_diff_elo_pick), _es_mundial_pick)
            if _dc10["preferir_dc"]:
                r["sugerencia_dc10"] = _dc10["motivo"]
            # Guardar cuota como apertura para CLV posterior
            r["cuota_apertura"] = cuota
        else:
            r["edge"] = None
            r["movimiento"] = None
            r["b1_valido"] = True
            r["b2_vetar"] = False

    return recomendaciones

def preparar_analisis(fixture_id, incluir_odds=False, incluir_contexto=False):
    # Datos base del fixture: cacheados 1h (no cambian antes del partido)
    fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)

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

    # ── RECALIBRACION V14.2 ───────────────────────────────────────────
    # Se aplica DESPUES de enriquecer con odds para que el filtro de
    # cuota use la cuota real de mercado cuando exista.
    for r in recomendaciones:
        aplicar_recalibracion(r, liga=league)

    # ── BONUS H2H EN MERCADOS DE GOLES ────────────────────────────────
    # Si en los ultimos 5 H2H el mercado elegido fue consistente, +0.5 score.
    try:
        home_id_ha = fixture["teams"]["home"]["id"]
        away_id_ha = fixture["teams"]["away"]["id"]
        h2h_bonus = api_get(
            f"/fixtures/headtohead?h2h={home_id_ha}-{away_id_ha}&last=5",
            use_cache=True, ttl=7200
        )
        if h2h_bonus and len(h2h_bonus) >= 3:
            goles_h2h = [(m["goals"]["home"] or 0) + (m["goals"]["away"] or 0)
                         for m in h2h_bonus
                         if m["goals"]["home"] is not None]
            if goles_h2h:
                over15_h2h = sum(1 for g in goles_h2h if g >= 2) / len(goles_h2h)
                under35_h2h = sum(1 for g in goles_h2h if g <= 3) / len(goles_h2h)
                prom_h2h = sum(goles_h2h) / len(goles_h2h)

                # V14.3 FIX: Descarte directo por contradicción H2H.
                # Si el promedio de goles H2H supera la línea, el pick Under
                # es estadísticamente contradictorio y se elimina.
                # Ej: promedio H2H 4.0 goles → Under 3.5 no tiene sentido.
                recomendaciones = [
                    r for r in recomendaciones
                    if not (
                        ("under 3.5" in (r.get("jugada") or "").lower() and prom_h2h >= 3.5)
                        or ("under 2.5" in (r.get("jugada") or "").lower() and prom_h2h >= 2.5)
                        or ("under 1.5" in (r.get("jugada") or "").lower() and prom_h2h >= 1.5)
                    )
                ]

                for r in recomendaciones:
                    jugada_r = (r.get("jugada") or "").lower()
                    if "over 1.5" in jugada_r and over15_h2h >= 0.7:
                        r["score"] = round(min(10.0, r["score"] + 0.5), 1)
                        r["motivo"] = r.get("motivo", "") + f" H2H refuerza Over1.5 ({int(over15_h2h*100)}%)."
                    elif ("over 2.5" in jugada_r) and over15_h2h >= 0.8:
                        r["score"] = round(min(10.0, r["score"] + 0.3), 1)
                    elif "under 3.5" in jugada_r and under35_h2h >= 0.8:
                        r["score"] = round(min(10.0, r["score"] + 0.5), 1)
                        r["motivo"] = r.get("motivo", "") + f" H2H refuerza Under3.5 ({int(under35_h2h*100)}%)."
    except Exception as e:
        print(f"WARN H2H bonus: {e}")

    # ── xG DE PREDICTIONS COMO SEÑAL PREMATCH ─────────────────────────
    # /predictions devuelve goles esperados por equipo — usarlos para
    # reforzar o penalizar mercados de goles.
    try:
        pred_data = api_get(
            f"/predictions?fixture={fixture_id}",
            use_cache=True, ttl=3600
        )
        if pred_data:
            p0 = pred_data[0] if isinstance(pred_data, list) else pred_data
            goals_pred = p0.get("predictions", {}).get("goals", {})
            xg_home = float(goals_pred.get("home", 0) or 0)
            xg_away = float(goals_pred.get("away", 0) or 0)
            xg_total = round(xg_home + xg_away, 2)
            if xg_total > 0:
                for r in recomendaciones:
                    jugada_r = (r.get("jugada") or "").lower()
                    if "over 1.5" in jugada_r:
                        if xg_total >= 2.5:
                            r["score"] = round(min(10.0, r["score"] + 0.4), 1)
                        elif xg_total < 1.2:
                            r["score"] = round(max(0.0, r["score"] - 0.3), 1)
                    elif "over 2.5" in jugada_r:
                        if xg_total >= 3.0:
                            r["score"] = round(min(10.0, r["score"] + 0.4), 1)
                        elif xg_total < 1.8:
                            r["score"] = round(max(0.0, r["score"] - 0.3), 1)
                    elif "under 3.5" in jugada_r:
                        if xg_total <= 2.0:
                            r["score"] = round(min(10.0, r["score"] + 0.3), 1)
                        elif xg_total > 3.0:
                            r["score"] = round(max(0.0, r["score"] - 0.4), 1)
                    # Guardar xG en el pick para aprendizaje ML
                    r["xg_pred_home"] = xg_home
                    r["xg_pred_away"] = xg_away
                    r["xg_pred_total"] = xg_total
    except Exception as e:
        print(f"WARN xG predictions: {e}")

    # ── MOTIVACIÓN DINÁMICA V14.3 ──────────────────────────────────────
    # Ajusta el score según la situación real de los equipos en la tabla.
    # Equipos con alta motivación (descenso, título) juegan con más intensidad.
    # Equipos sin nada que ganar (mid-table asegurado) juegan con menos urgencia.
    try:
        standings_data = api_get(
            f"/standings?league={fixture['league']['id']}&season={fixture['league']['season']}",
            use_cache=True, ttl=7200
        )
        if standings_data:
            # Construir mapa posición por team_id
            pos_map = {}
            total_equipos = 0
            for grupo in standings_data:
                for liga_std in grupo.get("league", {}).get("standings", []):
                    total_equipos = max(total_equipos, len(liga_std))
                    for entry in liga_std:
                        tid = entry.get("team", {}).get("id")
                        pos = entry.get("rank", 99)
                        if tid:
                            pos_map[tid] = pos

            if total_equipos > 0 and pos_map:
                def _motivacion(team_id, pos, total):
                    """
                    Retorna ajuste de score por motivación:
                    +0.5 lucha título (top 2) o zona descenso (últimos 3)
                    +0.3 lucha clasificación europea (top 6) o playoff descenso
                    -0.3 mid-table sin objetivos (posición central asegurada)
                    """
                    if total < 6:
                        return 0.0  # Torneo corto, no aplica
                    pct = pos / total
                    if pos <= 2:
                        return 0.5   # Lucha por el título
                    elif pos <= 6:
                        return 0.3   # Lucha por Europa
                    elif pct >= 0.85:
                        return 0.5   # Zona de descenso (últimos 15%)
                    elif pct >= 0.75:
                        return 0.3   # Playoff descenso
                    elif 0.35 <= pct <= 0.65:
                        return -0.3  # Mid-table sin objetivos
                    return 0.0

                mot_home = _motivacion(home_id, pos_map.get(home_id, 99), total_equipos)
                mot_away = _motivacion(away_id, pos_map.get(away_id, 99), total_equipos)
                ajuste_mot = round((mot_home + mot_away) / 2, 1)

                if ajuste_mot != 0:
                    for r in recomendaciones:
                        r["score"] = round(clamp(r["score"] + ajuste_mot, 0, 10), 1)
                        if ajuste_mot > 0:
                            r["motivo"] = r.get("motivo", "") + f" Motivación alta (+{ajuste_mot})."
                        else:
                            r["motivo"] = r.get("motivo", "") + f" Motivación baja ({ajuste_mot})."
    except Exception as e:
        print(f"WARN motivacion dinamica: {e}")

    # Filtro de cuota minima: descarta picks que no pueden ser rentables.
    recomendaciones = [
        r for r in recomendaciones if cuota_pick_suficiente(r)
    ]
    # ── V15 B1: Descartar si cuota real < 90% de la teórica ──────────
    recomendaciones = [r for r in recomendaciones if r.get("b1_valido", True)]
    # ── V15 B2: Descartar si discrepancia modelo vs Pinnacle > 15pp ───
    recomendaciones = [r for r in recomendaciones if not r.get("b2_vetar", False)]
    # ── V15b D3: Veto global score < 7.0 ─────────────────────────────
    recomendaciones = [r for r in recomendaciones if not veto_score_minimo_global(r.get("score", 0))]
    # ── V15b D4: Limite 2 picks por mercado (anti-sobreexposicion) ────
    _picks_por_mercado: dict = {}
    _recomendaciones_limitadas = []
    for _r in recomendaciones:
        _m = _r.get("mercado", "").lower()
        _picks_por_mercado[_m] = _picks_por_mercado.get(_m, 0)
        if not verificar_limite_picks_mercado(
            [{"mercado": _m}] * _picks_por_mercado[_m], _m, max_por_mercado=2
        ):
            _picks_por_mercado[_m] += 1
            _recomendaciones_limitadas.append(_r)
    recomendaciones = _recomendaciones_limitadas

    # ── FILTRO DE EDGE POSITIVO OBLIGATORIO ───────────────────────────
    # Solo pasan picks donde el mercado paga mas de lo que Pinnacle implica.
    # Si no hay cuota de Pinnacle se permite (edge=None -> no penalizar).
    recomendaciones = [
        r for r in recomendaciones
        if r.get("edge") is None or r.get("edge", 0) >= 0
    ]

    # ── FILTRO DE SCORE DINAMICO POR CUOTA ────────────────────────────
    # Mas cuota = mas score exigido (el modelo debe estar mas convencido).
    def _score_min_para_cuota(cuota):
        for c_min, c_max, s_min in SCORE_MIN_POR_CUOTA:
            if c_min <= cuota <= c_max:
                return s_min
        return 7.5

    def _pasa_filtro_score_cuota(r):
        cuota = _cuota_segura(r)
        if cuota <= 0:
            return True   # sin cuota real no penalizar
        score = float(r.get("score", 0) or 0)
        return score >= _score_min_para_cuota(cuota)

    recomendaciones = [r for r in recomendaciones if _pasa_filtro_score_cuota(r)]

    # ── FILTRO DE MERCADOS CONSERVADOR ────────────────────────────────
    recomendaciones = [
        r for r in recomendaciones
        if r.get("mercado", "") in MERCADOS_CONSERVADOR
    ]

    # ── ORDENAR: score primario, VE como desempate ─────────────────────
    # V14.2: score vuelve a ser el criterio principal.
    # VE (prob * cuota) rompe empates entre picks con mismo score.
    def _clave_orden(x):
        score = float(x.get("score", 0) or 0)
        prob = float(x.get("prob", 0) or 0) / 100.0
        cuota = _cuota_segura(x)
        ve = prob * cuota
        return (score, ve)

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
        "fecha": fecha_hoy_peru(),          # fecha Peru al momento de guardar
        "fecha_partido": fecha_hoy_peru(),  # mismo — el partido es hoy (live)
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

        # B: Saltar fixture_id sinteticos (REC-xxxx) generados por reconstruccion
        if not fixture_id or str(fixture_id).startswith("REC-"):
            continue

        try:
            fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=False)
        except Exception as e:
            print(f"WARN actualizar fixture {fixture_id}: {e}")
            continue

        if not fixture:
            continue

        fixture = fixture[0]
        status = fixture["fixture"]["status"]["short"]

        # Corregir hora del pick si esta mal (reconvertir de UTC a Peru)
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

        try:
            stats = api_get(f"/fixtures/statistics?fixture={fixture_id}", use_cache=False)
        except Exception:
            stats = None

        if stats:
            total_corners = 0
            total_cards = 0

            for team_data in stats:
                for item in team_data.get("statistics", []):
                    tipo = item.get("type")
                    raw = item.get("value")

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

        # ── HT (primer tiempo) — usar marcador de halftime, NO el final ──
        if "ht" in jugada_lower and ("over" in jugada_lower or "under" in jugada_lower):
            linea = _linea(jugada)
            # Intentar obtener marcador de primer tiempo desde la API
            try:
                score_ht = fixture.get("score", {}).get("halftime", {})
                gh_ht = score_ht.get("home")
                ga_ht = score_ht.get("away")
                if gh_ht is not None and ga_ht is not None:
                    total_ht = gh_ht + ga_ht
                    if "over" in jugada_lower:
                        acierto = total_ht > linea if linea is not None else None
                    else:
                        acierto = total_ht < linea if linea is not None else None
                    p["resultado_real"] = f"HT {gh_ht}-{ga_ht}"
                else:
                    # Sin datos HT, dejar pendiente_manual
                    p["estado"] = "pendiente_manual"
                    p["resultado"] = "pendiente_manual"
                    continue
            except Exception:
                p["estado"] = "pendiente_manual"
                p["resultado"] = "pendiente_manual"
                continue

        # ── Goles ────────────────────────────────────────────────────────
        elif "under" in jugada_lower and "gol" in jugada_lower:
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

        # ── Sin Tarjeta Roja ─────────────────────────────────────────────
        elif "sin tarjeta roja" in jugada_lower:
            rojas_pick = 0
            stats_disponibles = False
            if stats:
                for td_sr in stats:
                    stats_disponibles = True
                    for item_sr in td_sr.get("statistics", []):
                        if item_sr.get("type") == "Red Cards":
                            val_sr = item_sr.get("value")
                            if val_sr is not None:
                                try:
                                    rojas_pick += int(str(val_sr))
                                except Exception:
                                    pass
            # Si no hay estadisticas disponibles (liga menor), dejar pendiente_manual
            if not stats_disponibles:
                p["estado"] = "pendiente_manual"
                p["resultado"] = "pendiente_manual"
                p["resultado_real"] = "Sin stats API — verificar manual"
                continue
            acierto = rojas_pick == 0
            p["resultado_real"] = f"{rojas_pick} rojas"

        if "Corners" in jugada:
            p["resultado_real"] = f"{corners_total} corners"
        elif "Tarjetas" in jugada:
            p["resultado_real"] = f"{tarjetas_total} tarjetas"
        elif "resultado_real" not in p:
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
        except Exception as e:
            print(f"WARN _actualizar_resultado_combinada: {e}")

    return picks, cambios


async def _enviar_mensaje_paginado(update, texto, parse_mode="Markdown", chunk=3900):
    """Divide mensajes largos en partes para no superar el limite de Telegram."""
    texto = (texto or "").strip()
    if not texto:
        return
    # Limpiar Markdown mal formado antes de enviar
    if parse_mode == "Markdown":
        texto = _safe_send_md(texto)
    if len(texto) <= chunk:
        try:
            await update.message.reply_text(texto, parse_mode=parse_mode)
        except Exception:
            # Fallback sin formato si hay error de parse entities
            await update.message.reply_text(
                texto.replace("*","").replace("_","").replace("`",""),
                parse_mode=None
            )
        return
    partes = []
    while texto:
        partes.append(texto[:chunk])
        texto = texto[chunk:]
    for i, parte in enumerate(partes):
        sufijo = f"\n_(parte {i+1}/{len(partes)})_" if len(partes) > 1 else ""
        try:
            await update.message.reply_text(parte + sufijo, parse_mode=parse_mode)
        except Exception:
            # Fallback sin formato
            texto_limpio = (parte + sufijo).replace("*","").replace("_","").replace("`","")
            try:
                await update.message.reply_text(texto_limpio, parse_mode=None)
            except Exception:
                pass


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


def texto_resumen(data, mini_tickets=None):
    recs = data["recomendaciones"]

    texto = (
        f"⚽ {data['home']} vs {data['away']}\n"
        f"🏆 {data['country']} - {data['league']}\n"
        f"🕒 {data['hora']} Hora Perú\n\n"
    )

    if not recs:
        texto += "⚠️ No hay jugada clara.\nRecomendación: NO apostar."
    else:
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

    # Sección mini-tickets del mismo partido
    if mini_tickets:
        texto += "\n\n━━━━━━━━━━\n💡 *Mini-tickets sugeridos para este partido:*\n"
        for i, mt in enumerate(mini_tickets[:3], 1):
            picks_txt = " + ".join(
                f"{e['jugada']} ({e['cuota']}x)" for e in mt["picks"]
            )
            est_txt = " ⚠️est." if any(e.get("cuota_estimada") for e in mt["picks"]) else ""
            texto += (
                f"\n🎫 *Ticket {i}* — cuota {mt['cuota_combinada']}x{est_txt}\n"
                f"   {picks_txt}\n"
                f"   Prob conjunta: ~{mt['prob_conjunta']}%\n"
            )
        texto += "\n_(Cuotas marcadas con ⚠️est. son estimadas — verifica en tu casa de apuestas)_"

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
        time.sleep(0.25)  # Anti-ráfaga 429

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
    ligas.update(SELECCIONES_LEAGUES)

    partidos = []

    for league_name, data in ligas.items():
        fixtures = api_get(
            f"/fixtures?league={data['id']}&season={data['season']}&date={today}",
            use_cache=True,
            ttl=600
        )
        time.sleep(0.25)  # Anti-ráfaga: pausa entre peticiones de ligas

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

    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)
    ligas.update(SELECCIONES_LEAGUES)

    today = fecha_hoy_peru()

    for _, data_liga in ligas.items():

        fixtures = api_get(
            f"/fixtures?league={data_liga['id']}&season={data_liga['season']}&date={today}",
            use_cache=True,
            ttl=600
        )
        time.sleep(0.25)  # Anti-ráfaga

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

                # V14.2: filtrar por SCORE como criterio principal
                score_top = float(top.get("score", 0) or 0)
                if score_top < score_minimo:
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

    # Ordenar: score descendente, riesgo ascendente como desempate
    oportunidades.sort(
        key=lambda x: (float(x.get("score", 0) or 0),
                       -int(x.get("riesgo", 9) or 9),
                       float(x.get("prob", 0) or 0)),
        reverse=True,
    )

    return oportunidades[:MAX_PICKS_DIA]

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
    # V17: Mostrar match type y nivel de confianza OU25
    _match_type = rec.get("match_type","") if isinstance(rec, dict) else ""
    _ou25_nivel = rec.get("ou25_nivel","") if isinstance(rec, dict) else ""
    if _match_type and _match_type != "standard":
        _mt_emoji = {"top_vs_top":"⚖️","top_vs_bottom":"⬆️","relegation":"🔥",
                      "cup_final":"🏆","dead_rubber":"😴"}.get(_match_type,"📊")
        lineas.append(f"{_mt_emoji} Tipo partido: {_match_type}")
    if _ou25_nivel in ("ELITE","ALTA"):
        lineas.append(f"🎯 Sistema O/U 2.5: {_ou25_nivel}")

    # V16: Mostrar descripción motivacional del standings si hay
    _desc_home = rec.get("home_descripcion") if isinstance(rec, dict) else None
    _desc_away = rec.get("away_descripcion") if isinstance(rec, dict) else None
    if _desc_home or _desc_away:
        _desc_txt = []
        if _desc_home: _desc_txt.append(f"Local: {_desc_home}")
        if _desc_away: _desc_txt.append(f"Visita: {_desc_away}")
        lineas.append("📋 " + " | ".join(_desc_txt))

    # D5: Badge de confianza visual
    lineas.append(f"🏷️ {badge_confianza(score)}")
    # D6: Alerta elite máximo
    if es_alerta_elite(score):
        lineas.append("🚨 PICK ELITE MÁXIMO — score 9.5+")
    # V14.3: Stake Kelly fraccionado como referencia
    if cuota_mostrar and cuota_mostrar > 1.0 and prob > 0:
        try:
            from datetime import date as _kd
            bank_data = leer_json(BANK_ACUMULADO_FILE)
            bank_kelly = bank_data[-1].get("bank", BANK_INICIAL) if bank_data else BANK_INICIAL
            stake_k, kelly_pct = calcular_stake_kelly(prob / 100, cuota_mostrar, bank_kelly)
            # V15: Sistema de 3 niveles de stake por score
            score_pick = float(rec.get("score", 0) if isinstance(rec, dict) else 0)
            stake_v15 = calcular_stake_v15(score_pick, prob, cuota_mostrar, bank_kelly)
            # N14: Kelly dinámico — 1/4 vs 1/2 según confirmación Pinnacle
            _confirmado_pinnacle = rec.get("edge", 0) and float(rec.get("edge", 0) or 0) > 0.03
            _stake_kelly_din = kelly_dinamico(prob, cuota_mostrar, bank_kelly, confirmado_pinnacle=bool(_confirmado_pinnacle))
            if stake_v15["nivel"] > 0:
                lineas.append(f"💰 {stake_v15['descripcion']}: S/{stake_v15['stake']:.1f}")
            elif kelly_pct > 0:
                lineas.append(f"📊 Kelly ref: S/{stake_k:.1f} ({kelly_pct:.1f}% Kelly → 25% fracc.)")
        except Exception:
            pass
    # V16: Mostrar señal under_over de la API si está disponible
    _uo = rec.get("api_under_over") if isinstance(rec, dict) else None
    if _uo:
        _uo_emoji = "⬆️" if _uo == "+2.5" else "⬇️"
        lineas.append(f"{_uo_emoji} API señala: {_uo} goles")
    # V16: Mostrar scoring first probability si hay datos HT
    _sfp = rec.get("scoring_first_prob") if isinstance(rec, dict) else None
    if _sfp and float(_sfp) > 0.70:
        lineas.append(f"⚡ Prob. marcar primero: {float(_sfp):.0%}")

    # CQ5/P7: Sugerir correcto resultado como eslabón de alta cuota
    try:
        _prob_home_win = float(rec.get("prob", 50) if isinstance(rec, dict) else 50)
        _xg_total_msg = float(rec.get("xg_pred_total") or total_prom if "total_prom" in dir() else 2.5)
        _liga_msg = rec.get("liga", "") if isinstance(rec, dict) else ""
        _cr = recomendar_correcto_resultado(_liga_msg, _prob_home_win, _xg_total_msg)
        if _cr:
            lineas.append(f"📌 Resultado frecuente: {_cr['resultado']} (~{_cr['prob_estimada']}%) — útil como eslabón ticket")
    except Exception:
        pass

    if mostrar_id and fixture_id:
        lineas.append(f"\U0001f4cc ID: {fixture_id}")

    return "\n".join(lineas)


def generar_top_fecha(fecha, score_minimo=7.5):
    # V17: Verificar si hay congestión alta que afecte picks
    # (la congestión se evalúa por equipo en evaluar_sistema_ou25_especializado)
    # D8: Ajustar score mínimo si hay racha de fallos
    try:
        _datos_ap = leer_json(APRENDIZAJE_FILE)
        _ultimos = [e.get("resultado","") for e in (_datos_ap or [])[-10:]]
        _racha_fallos = 0
        for _r in reversed(_ultimos):
            if str(_r).lower() in ("fallo","loss","l"): _racha_fallos += 1
            else: break
        _ajuste_racha = ajuste_volumen_por_racha(_racha_fallos)
        if _ajuste_racha["score_minimo_ajustado"]:
            score_minimo = max(score_minimo, _ajuste_racha["score_minimo_ajustado"])
    except Exception:
        pass
    oportunidades = []

    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)
    ligas.update(SELECCIONES_LEAGUES)

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

            # V14.2: score como criterio principal
            score_top = float(top.get("score", 0) or 0)
            if score_top < score_minimo:
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
        key=lambda x: float(x.get("score", 0) or 0),
        reverse=True
    )

    return oportunidades[:MAX_PICKS_DIA]

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
            # ── V16: Nuevos campos de /fixtures/statistics ─────────────
            elif tipo == "Shots insidebox":
                stats[name]["shots_insidebox"] = valor      # xG/shot quality
            elif tipo == "Shots outsidebox":
                stats[name]["shots_outsidebox"] = valor
            elif tipo == "Blocked Shots":
                stats[name]["blocked_shots"] = valor        # defensive pressure
            elif tipo == "Fouls":
                stats[name]["fouls"] = valor                # PPDA proxy + tarjetas
            elif tipo == "Goalkeeper Saves":
                stats[name]["goalkeeper_saves"] = valor     # shot quality rival
            elif tipo == "Passes accurate":
                stats[name]["passes_accurate"] = valor      # possession quality
            elif tipo in ("Passes %", "Passes%"):
                stats[name]["passes_pct"] = valor           # precision pases
            elif tipo == "Attacks":
                stats[name]["attacks_total"] = valor        # entradas tercio final
            elif tipo == "Offsides":
                stats[name]["offsides"] = valor             # pressing alto proxy

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

        # Refrescar la cuota con la cuota REAL EN VIVO antes de guardar.
        # La cuota estimada del modelo (ej: cuota_corner de linea_corners_recomendada)
        # es estatica y puede diferir mucho de la cuota live real del mercado.
        try:
            cuota_live_real, book_live_real = buscar_cuota_live(
                fixture_id, top_live.get("jugada", "")
            )
            if cuota_live_real and cuota_live_real > 1.0:
                top_live["cuota"] = cuota_live_real
                top_live["cuota_api"] = cuota_live_real
                top_live["bookmaker"] = book_live_real
        except Exception as e:
            print(f"WARN cuota live en analizar_live_fixture: {e}")

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

    # ── Seccion combinadas y mini-tickets del dia ────────────────────
    y -= 10
    c.setFont("Helvetica-Bold", 12)
    c.drawString(40, y, "COMBINADA DEL DIA")
    y -= 20
    c.setFont("Helvetica", 10)

    comb_hoy = None
    mini_tickets_hoy = []
    try:
        combinadas = leer_json(COMBINADAS_FILE)
        # Combinada principal (no MT)
        comb_hoy = next(
            (c2 for c2 in combinadas
             if c2.get("fecha") == hoy
             and c2.get("subtipo") not in ("MT",)
             and not c2.get("sin_combinada")
             and c2.get("picks")),
            None
        )
        # Mini-tickets del dia
        mini_tickets_hoy = [
            c2 for c2 in combinadas
            if c2.get("fecha") == hoy
            and c2.get("subtipo") == "MT"
            and c2.get("picks")
        ]
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
            estado_pk = pk.get("estado", "pendiente")
            linea = f"  {i}. {pk.get('partido','')} — {pk.get('jugada','')} | Score: {pk.get('score','')} | Cuota: {cuota_p} | {estado_pk.upper()}"
            c.drawString(40, y, linea[:110])
            y -= 14
        # Solo mostrar "Fallo en" si el estado real es fallo
        if comb_hoy.get("estado","").lower() == "fallo" and comb_hoy.get("fallo_en"):
            c.drawString(40, y, f"  Fallo en: {comb_hoy.get('fallo_en','')}")
            y -= 14
    elif comb_hoy and comb_hoy.get("sin_combinada"):
        c.drawString(40, y, f"Sin combinada rentable: {comb_hoy.get('motivo','')}")
        y -= 14
    else:
        c.drawString(40, y, "No se genero combinada hoy (usa /combinada_dia para generarla)")
        y -= 14

    # Mini-tickets del dia
    if mini_tickets_hoy:
        y -= 10
        c.setFont("Helvetica-Bold", 11)
        c.drawString(40, y, f"MINI-TICKETS DEL DIA ({len(mini_tickets_hoy)} tickets)")
        y -= 16
        c.setFont("Helvetica", 9)
        for mt in mini_tickets_hoy:
            estado_mt = mt.get("estado", "pendiente").upper()
            cuota_mt = mt.get("cuota_combinada", "?")
            prob_mt = mt.get("prob_conjunta", "?")
            ticket_id = mt.get("ticket_id", "")
            c.drawString(40, y, f"Ticket: {ticket_id} | Cuota: {cuota_mt}x | Prob: {prob_mt}% | Estado: {estado_mt}")
            y -= 12
            for i, pk in enumerate(mt.get("picks", []), 1):
                cuota_p = pk.get("cuota") or "?"
                estado_pk = pk.get("estado", "pendiente")
                linea = f"  {i}. {pk.get('partido','')} — {pk.get('jugada','')} | {cuota_p}x | {estado_pk.upper()}"
                c.drawString(40, y, linea[:110])
                y -= 11
            y -= 5
            if y < 80:
                c.showPage()
                y = 780
                c.setFont("Helvetica", 9)

    # ── Seccion handicap del dia ──────────────────────────────────────
    y = _seccion_handicap_pdf(c, y, hoy)

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
            _seccion_handicap_historico_pdf(elements, fechas_ord[0], fechas_ord[-1], styles)

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
        # Siempre actualizar picks individuales (no solo cuando hay combinadas)
        actualizar_resultados_automaticos()
        _actualizar_resultado_combinada()

        # Verificar cuales combinadas cambiaron
        combinadas_antes = leer_json(COMBINADAS_FILE)
        pendientes_antes = {
            c.get("ticket_id",""): c.get("estado","pendiente")
            for c in combinadas_antes
            if c.get("estado","pendiente") == "pendiente"
            and not c.get("sin_combinada")
        }

        combinadas_despues = leer_json(COMBINADAS_FILE)
        chat_id = context.job.chat_id

        for c in combinadas_despues:
            ticket = c.get("ticket_id","")
            if ticket not in pendientes_antes:
                continue
            nuevo_estado = c.get("estado","pendiente")
            if nuevo_estado == pendientes_antes[ticket]:
                continue
            if nuevo_estado.lower() == "acierto":
                emoji = "✅"
                cuota = c.get("cuota_combinada", "?")
                picks_txt = " + ".join(
                    p.get("jugada","?") for p in c.get("picks",[])
                )
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=(
                        f"{emoji} *COMBINADA CERRADA — ACIERTO*\n"
                        f"Ticket: {ticket}\n"
                        f"Cuota: {cuota}x\n"
                        f"Picks: {picks_txt}"
                    ),
                    parse_mode="Markdown"
                )
            elif nuevo_estado.lower() == "fallo":
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=f"❌ *Combinada {ticket} — fallo*",
                    parse_mode="Markdown"
                )
    except Exception as e:
        print(f"ERROR _check_combinadas_job: {e}")


async def _job_actualizar_estados(context: ContextTypes.DEFAULT_TYPE):
    """
    Job global cada 20 minutos: actualiza estados de picks y combinadas
    pendientes automaticamente, independientemente de si hay alertas activas.
    Tambien detecta rachas de fallos y freno de bank.
    """
    try:
        picks, cambios = actualizar_resultados_automaticos()
        if cambios > 0:
            print(f"[auto-update] {cambios} picks actualizados")

        # Cerrar handicaps pendientes
        try:
            cambios_ha = cerrar_handicaps_pendientes()
            if cambios_ha > 0:
                print(f"[handicap] {cambios_ha} picks cerrados automaticamente")
        except Exception as e:
            print(f"WARN cerrar_handicaps: {e}")

        # V: Alerta de racha de fallos consecutivos
        picks_cerrados_recientes = [
            p for p in picks
            if p.get("estado", "").lower() in ("acierto", "fallo")
        ]
        picks_cerrados_recientes.sort(
            key=lambda p: p.get("timestamp", ""), reverse=True
        )
        ultimos = picks_cerrados_recientes[:RACHA_FALLOS_ALERTA]
        if (len(ultimos) == RACHA_FALLOS_ALERTA
                and all(p.get("estado") == "fallo" for p in ultimos)):
            chats = _cargar_chat_ids_alarmas()
            for cid in chats:
                try:
                    await context.bot.send_message(
                        chat_id=cid,
                        text=(
                            f"⚠️ *ALERTA: {RACHA_FALLOS_ALERTA} fallos consecutivos*\n"
                            f"El sistema detectó una racha negativa. "
                            f"Considera revisar los criterios antes de continuar."
                        ),
                        parse_mode="Markdown"
                    )
                except Exception:
                    pass

        # U: Freno de bank
        try:
            bank_data = _leer_bank_acumulado()
            if bank_data:
                bank_actual = bank_data[-1].get("bank", BANK_INICIAL)
                freno = BANK_INICIAL * BANK_FRENO_PCT
                if bank_actual <= freno:
                    chats = _cargar_chat_ids_alarmas()
                    for cid in chats:
                        try:
                            await context.bot.send_message(
                                chat_id=cid,
                                text=(
                                    f"🛑 *FRENO DE BANK ACTIVADO*\n"
                                    f"Bank actual: S/ {bank_actual:.2f} "
                                    f"(límite: S/ {freno:.2f})\n"
                                    f"No se generarán nuevos picks hasta revisión manual."
                                ),
                                parse_mode="Markdown"
                            )
                        except Exception:
                            pass
        except Exception as e:
            print(f"WARN freno bank: {e}")

    except Exception as e:
        print(f"ERROR _job_actualizar_estados: {e}")
    """
    Job periodico cada 15 minutos.
    Actualiza resultados de picks y combinadas pendientes automaticamente.
    Si alguna combinada se cierra, notifica al chat.
    """
    try:
        # Siempre actualizar picks individuales (no solo cuando hay combinadas)
        actualizar_resultados_automaticos()
        _actualizar_resultado_combinada()

        # Verificar cuales combinadas cambiaron
        combinadas_antes = leer_json(COMBINADAS_FILE)
        pendientes_antes = {
            c.get("ticket_id",""): c.get("estado","pendiente")
            for c in combinadas_antes
            if c.get("estado","pendiente") == "pendiente"
            and not c.get("sin_combinada")
        }

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

    # Job combinada garantizada diaria — 7:30 AM hora Peru (12:30 UTC)
    for job in context.job_queue.get_jobs_by_name(f"combinada_dia_{chat_id}"):
        job.schedule_removal()

    context.job_queue.run_daily(
        enviar_combinada_dia,
        time=dtime(hour=12, minute=30),  # 12:30 UTC = 7:30 AM Peru
        days=tuple(range(7)),
        chat_id=chat_id,
        name=f"combinada_dia_{chat_id}"
    )

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
        time.sleep(0.25)  # Anti-ráfaga 429

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
                "country": country,
                "round": m["league"].get("round", ""),
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
    await update.message.reply_text("📅 Buscando fixtures de mañana (todas las ligas + selecciones)...")

    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)
    ligas.update(SELECCIONES_LEAGUES)

    fecha = fecha_manana_peru()

    texto = texto_fixtures_fecha(
        "FIXTURES MAÑANA — TODAS LAS LIGAS + SELECCIONES",
        ligas,
        fecha
    )

    await _enviar_mensaje_paginado(update, texto, parse_mode=None)


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
        "🤖 *HarryNine V14.2* activo 😎🔥\n"
        "━━━━━━━━━━\n"
        "📋 *FIXTURES*\n"
        "/fixtures — Partidos de hoy (todas las ligas)\n"
        "/fixtures_manana — Manana todas\n"
        "━━━━━━━━━━\n"
        "🔍 *ANALISIS*\n"
        "/analizar_all — Analiza TODAS las ligas + selecciones + Mundial\n"
        "/analizar — Mini-tickets del día (sin ID)\n"
        "/analizar ID — Analiza un partido específico + mini-tickets\n"
        "/detalle ID — Detalle completo de un partido\n"
        "/scanear — Escanea todas las ligas\n"
        "━━━━━━━━━━\n"
        "🎫 *MINI-TICKETS Y COMBINADAS*\n"
        "/analizar — Mini-tickets del día (Doble Op + Goles + Sin Roja)\n"
        "/combinada_dia — Combinada garantizada del día (S/25 fijos)\n"
        "/combinada — Combinada óptima prematch del día\n"
        "/combinada_live — Combinada óptima picks live ahora\n"
        "/combinada_mixta — Combinada mixta prematch + live\n"
        "/comb3 /comb4 /comb5 — Combinadas cuota alta\n"
        "━━━━━━━━━━\n"
        "📊 *REPORTES*\n"
        "/resumen — Resumen del dia (actualiza estados)\n"
        "/resumen_ayer — Resumen de ayer + combinadas\n"
        "/resumen_prematch — Solo picks prematch de hoy\n"
        "/resumen_live — Solo picks live de hoy\n"
        "/resumen_combinadas — Solo combinadas de hoy\n"
        "/estado — Dashboard rapido del dia\n"
        "/escalera — Escalera cronologica de picks\n"
        "/rendimiento — Reporte de rendimiento + bank\n"
        "/pdf_semana — Reporte semanal PDF\n"
        "/pdf_mes — Reporte mensual PDF\n"
        "━━━━━━━━━━\n"
        "🔧 *UTILIDADES*\n"
        "/feedback ID acierto|fallo — Marcar resultado\n"
        "━━━━━━━━━━\n"
        "🔬 *HANDICAP ASIÁTICO*\n"
        "/handicap — Picks de handicap del día (modo observación)\n"
        "/handicap_stats — Estadísticas acumuladas de handicap\n"
        "━━━━━━━━━━\n"
        "⏰ *AUTOMATICO*\n"
        "Estados: actualiza cada 20 min\n"
        "Semanal: domingos 9:00 PM hora Peru\n"
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
    # Sin ID — muestra mini-tickets del dia
    if not context.args:
        _registrar_chat_alarma(update.effective_chat.id)
        hoy = fecha_hoy_peru()

        # Verificar si ya hay tickets generados hoy (cache del dia)
        combinadas_hoy = leer_json(COMBINADAS_FILE)
        mt_hoy = [c for c in combinadas_hoy
                  if c.get("subtipo") == "MT"
                  and c.get("fecha","")[:10] == hoy
                  and c.get("estado") == "pendiente"]

        if mt_hoy:
            # Ya hay tickets del dia — mostrar los existentes sin regenerar
            texto = f"💡 *Mini-tickets del día — {hoy}*\n"
            texto += f"_{len(mt_hoy)} tickets (generados anteriormente hoy)_\n"
            texto += "━━━━━━━━━━\n\n"

            for i, mt in enumerate(mt_hoy, 1):
                picks = mt.get("picks", [])
                n = len(picks)
                tipo = "Triple" if n == 3 else "Doble"
                cuota = mt.get("cuota_combinada", 1.0)
                prob = mt.get("prob_conjunta", 0)
                ticket_id = mt.get("ticket_id", "")
                ganancia_ref = round(10.0 * (cuota - 1), 2)

                texto += f"🎫 *Ticket {i} — {tipo}* | `{ticket_id}`\n"
                for j, e in enumerate(picks, 1):
                    mismo_partido = sum(1 for x in picks if x["fixture_id"] == e["fixture_id"]) > 1
                    est = " ⚠️est." if e.get("cuota_estimada") else ""
                    mismo_txt = " 🔄" if mismo_partido else ""
                    estado_e = e.get("estado","pendiente")
                    icono = "✅" if estado_e == "acierto" else "❌" if estado_e == "fallo" else "✅"
                    texto += (
                        f"  {j}. *{e['partido']}*{mismo_txt}\n"
                        f"     {e.get('league','')} | {e.get('hora','')}\n"
                        f"     {icono} {e['jugada']}\n"
                        f"     Cuota: {e['cuota']}x{est} | Prob: {e.get('prob',0)}%\n"
                    )
                texto += (
                    f"📊 Cuota total: *{cuota}x* | Prob conjunta: *~{prob}%*\n"
                    f"💰 Con S/10 → ganancia potencial: *S/ {ganancia_ref:.2f}*\n"
                    f"━━━━━━━━━━\n\n"
                )

            texto += "_(Usa /analizar refresh para regenerar los tickets del día)_"
            await _enviar_mensaje_paginado(update, texto)
            return

        await update.message.reply_text(
            "💡 Generando mini-tickets del día...\n"
            "Analizando todos los partidos disponibles. Esto puede tomar 1-2 minutos."
        )
        try:
            tickets = generar_mini_tickets_dia()
        except Exception as e:
            await update.message.reply_text(f"❌ Error generando mini-tickets: {e}")
            return

        if not tickets:
            await update.message.reply_text(
                "❌ No encontré mini-tickets válidos para hoy.\n"
                "Puede que no haya partidos disponibles o que las cuotas no alcancen el umbral mínimo."
            )
            return

        # Guardar tickets en combinadas.json para seguimiento
        for t in tickets:
            _guardar_combinada(t)

        # Formatear y enviar
        texto = f"💡 *Mini-tickets del día — {hoy}*\n"
        texto += f"_{len(tickets)} tickets sugeridos, ordenados por seguridad_\n"
        texto += "━━━━━━━━━━\n\n"

        for i, mt in enumerate(tickets, 1):
            picks = mt["picks"]
            n = mt["n_picks"]
            tipo = "Triple" if n == 3 else "Doble"
            cuota = mt["cuota_combinada"]
            prob = mt["prob_conjunta"]
            ticket_id = mt.get("ticket_id", "")
            stake_ref = 10.0
            ganancia_ref = round(stake_ref * (cuota - 1), 2)

            texto += f"🎫 *Ticket {i} — {tipo}* | `{ticket_id}`\n"
            for j, e in enumerate(picks, 1):
                mismo_partido = sum(1 for x in picks if x["fixture_id"] == e["fixture_id"]) > 1
                est = " ⚠️est." if e.get("cuota_estimada") else ""
                mismo_txt = " 🔄" if mismo_partido else ""
                texto += (
                    f"  {j}. *{e['partido']}*{mismo_txt}\n"
                    f"     {e['league']} | {e['hora']}\n"
                    f"     ✅ {e['jugada']}\n"
                    f"     Cuota: {e['cuota']}x{est} | Prob: {e['prob']}%\n"
                )
            texto += (
                f"📊 Cuota total: *{cuota}x* | Prob conjunta: *~{prob}%*\n"
                f"💰 Con S/10 → ganancia potencial: *S/ {ganancia_ref:.2f}*\n"
                f"━━━━━━━━━━\n\n"
            )

        texto += (
            "_(🔄 = mercados del mismo partido | ⚠️est. = cuota estimada, verifica en tu casa de apuestas)_\n"
            "_(Tickets guardados para seguimiento automático)_"
        )

        await _enviar_mensaje_paginado(update, texto)
        return

    # Con ID o "refresh"
    if context.args and context.args[0].lower() == "refresh":
        # Eliminar tickets pendientes del dia y regenerar
        hoy_r = fecha_hoy_peru()
        combinadas_r = leer_json(COMBINADAS_FILE)
        combinadas_r = [c for c in combinadas_r
                        if not (c.get("subtipo") == "MT"
                                and c.get("fecha","")[:10] == hoy_r
                                and c.get("estado") == "pendiente")]
        guardar_json_lista(COMBINADAS_FILE, combinadas_r)

        await update.message.reply_text(
            "🔄 Tickets del día eliminados. Regenerando...\n"
            "Esto puede tomar 1-2 minutos."
        )
        try:
            tickets_r = generar_mini_tickets_dia()
        except Exception as e:
            await update.message.reply_text(f"❌ Error: {e}")
            return
        if not tickets_r:
            await update.message.reply_text("❌ No encontré mini-tickets válidos para hoy.")
            return
        for t in tickets_r:
            _guardar_combinada(t)
        await update.message.reply_text(
            f"✅ {len(tickets_r)} tickets nuevos generados y guardados. Usa /analizar para verlos."
        )
        return

    # Con ID — análisis del partido específico
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

        await _enviar_mensaje_paginado(update, texto)
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

    # Generar mini-tickets del mismo partido
    mini_tickets_partido = []
    try:
        home_gen = data.get("home_general") or {}
        away_gen = data.get("away_general") or {}
        home = data["home"]
        away = data["away"]
        league = data["league"]
        country = data.get("country", "")
        hora = data["hora"]

        # Candidatos de eslabones para este partido
        eslabones_p = []
        for r in data.get("recomendaciones", []):
            cuota_r = _cuota_segura(r)
            prob_r = float(r.get("prob", 0) or 0)
            if MINI_TICKET_CUOTA_MIN <= cuota_r <= MINI_TICKET_CUOTA_MAX and prob_r >= max(60.0, 103.0 / max(cuota_r, 1.01)):
                eslabones_p.append({
                    "fixture_id": fixture_id,
                    "partido": f"{home} vs {away}",
                    "mercado": r.get("mercado", ""),
                    "jugada": r.get("jugada", ""),
                    "prob": prob_r,
                    "cuota": cuota_r,
                })

        # Sin Tarjeta Roja para este partido - solo con cuota real de Pinnacle
        fase_p = _detectar_fase_torneo(league, "")
        prob_sr = calcular_prob_sin_roja(home_gen, away_gen, fase_p)
        if prob_sr >= 75:
            odds_sr_p = api_get(f"/odds?fixture={fixture_id}", use_cache=True, ttl=600)
            cuota_sr_real = None
            if odds_sr_p:
                PINNACLE_NAMES_SR = {"Pinnacle", "Pinnacle Sports"}
                RED_CARD_MARKETS_SR = {"Red Card", "Will There Be a Red Card",
                                       "Red Cards", "Tarjeta Roja"}
                for casa_sr in odds_sr_p:
                    for book_sr in casa_sr.get("bookmakers", []):
                        if book_sr.get("name","") not in PINNACLE_NAMES_SR:
                            continue
                        for bet_sr in book_sr.get("bets", []):
                            if not any(rc.lower() in bet_sr.get("name","").lower()
                                       for rc in RED_CARD_MARKETS_SR):
                                continue
                            for val_sr in bet_sr.get("values", []):
                                if str(val_sr.get("value","")).lower() in ("no","nein","non"):
                                    try:
                                        c_r = float(val_sr.get("odd"))
                                        if c_r > 1.0:
                                            cuota_sr_real = round(c_r, 3)
                                    except Exception:
                                        pass
            if cuota_sr_real and MINI_TICKET_CUOTA_MIN <= cuota_sr_real <= MINI_TICKET_CUOTA_MAX:
                eslabones_p.append({
                    "fixture_id": fixture_id,
                    "partido": f"{home} vs {away}",
                    "mercado": "Sin Tarjeta Roja",
                    "jugada": "Sin Tarjeta Roja",
                    "prob": prob_sr,
                    "cuota": cuota_sr_real,
                })

        # Armar combinaciones de 2 eslabones del mismo partido
        from itertools import combinations as _comb_p
        for grupo_p in _comb_p(eslabones_p, 2):
            grupo_p = list(grupo_p)
            if not _son_compatibles(grupo_p[0]["jugada"], grupo_p[1]["jugada"]):
                continue
            cuota_p = round(grupo_p[0]["cuota"] * grupo_p[1]["cuota"], 2)
            prob_p = round(grupo_p[0]["prob"] / 100 * grupo_p[1]["prob"] / 100 * 100, 1)
            if MINI_TICKET_CUOTA_OBJ_MIN <= cuota_p <= MINI_TICKET_CUOTA_OBJ_MAX and prob_p >= MINI_TICKET_PROB_MIN:
                mini_tickets_partido.append({
                    "picks": grupo_p,
                    "cuota_combinada": cuota_p,
                    "prob_conjunta": prob_p,
                    "n_picks": 2,
                })

        mini_tickets_partido.sort(key=lambda t: t["prob_conjunta"], reverse=True)
    except Exception as e:
        print(f"WARN mini_tickets_partido {fixture_id}: {e}")

    await _enviar_mensaje_paginado(
        update,
        texto_resumen(data, mini_tickets=mini_tickets_partido[:3])
    )


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
        time.sleep(0.25)  # Anti-ráfaga
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
    ligas.update(SELECCIONES_LEAGUES)
    await fixtures_ligas(update, context, ligas, "Europa + Sudamérica + Selecciones + Mundial")


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
        time.sleep(0.25)  # Anti-ráfaga 429

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
    ligas.update(SELECCIONES_LEAGUES)

    await scanear_ligas(update, context, ligas, "Europa + Sudamérica + Selecciones + Mundial")


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
    # generar_top ya ordena correctamente por score — no re-ordenar aqui

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
    # Cuota se limita a 10.0 para evitar picks con cuotas incorrectas
    # (ej: cuotas de selecciones mal calculadas en versiones anteriores)
    profit = 0.0
    for p in cerrados:
        cuota = p.get("cuota_api") or p.get("cuota") or p.get("cuota_pinnacle") or p.get("cuota_minima") or 0
        try:
            cuota = float(cuota)
        except Exception:
            cuota = 0
        # Limitar cuota a rango razonable (max 10.0) para evitar distorsiones
        cuota = min(cuota, 10.0)
        if _es_acierto(p) and cuota > 1.0:
            profit += (cuota - 1)
        elif not _es_acierto(p):
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

    await update.message.reply_text("📄 Actualizando estados y generando resumen del día...")

    # C: Actualizar estados ANTES de construir el texto
    try:
        actualizar_resultados_automaticos()
    except Exception as e:
        print(f"WARN resumen actualizar: {e}")

    # PUNTO 5: resumen textual estilo Telegram (sin abrir archivos)
    try:
        picks_hoy = [p for p in leer_json(PICKS_FILE)
                     if p.get("fecha") == fecha_hoy_peru()
                     or p.get("fecha_partido") == fecha_hoy_peru()]
        texto = construir_resumen_textual(picks_hoy, "Resumen Diario")
        await _enviar_mensaje_paginado(update, texto)
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

    # Bloque handicap de ayer
    bloque_ha = ""
    try:
        ha_ayer = [r for r in leer_json(HANDICAP_FILE)
                   if r.get("fecha","")[:10] == ayer]
        if ha_ayer:
            cerrados_ha = [r for r in ha_ayer if r.get("estado") in ("acierto","fallo","push")]
            aciertos_ha = sum(1 for r in cerrados_ha if r.get("estado") == "acierto")
            fallos_ha = sum(1 for r in cerrados_ha if r.get("estado") == "fallo")
            push_ha = sum(1 for r in cerrados_ha if r.get("estado") == "push")
            validos_ha = aciertos_ha + fallos_ha
            ef_ha = round(aciertos_ha / validos_ha * 100, 1) if validos_ha else 0
            bloque_ha = (
                f"\n\n🔬 *Handicap Asiático ayer (observación):*\n"
                f"Total: {len(ha_ayer)} | Cerrados: {len(cerrados_ha)} | "
                f"✅ {aciertos_ha} | ❌ {fallos_ha} | 🔄 {push_ha} push\n"
                f"Efectividad: {ef_ha}%"
            )
    except Exception:
        pass

    mensaje = texto + "\n\n" + bloque_comb + bloque_ha
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

    # Tambien actualizar en HANDICAP_FILE si corresponde
    handicaps = leer_json(HANDICAP_FILE)
    for h in handicaps:
        if str(h.get("fixture_id")) == str(fixture_id):
            h["estado"] = resultado
            h["resultado"] = resultado
            actualizado = True
    guardar_json_lista(HANDICAP_FILE, handicaps)

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
STAKE_COMBINADA = 0.10
STAKE_COMBINADA_DIA = 25.0

# ── HANDICAP ASIATICO — MODO OBSERVACION ─────────────────────────────
HANDICAP_FILE = _tmp_path("handicap_seguimiento.json")
MAX_HANDICAP_DIA = 10          # maximo picks de handicap por dia
HANDICAP_CUOTA_MIN = 1.75      # cuota minima para que valga registrar
HANDICAP_PICKS_MIN_CONFIANZA = 30  # picks cerrados minimos para confiar

# Ligas que NO tienen estadisticas detalladas en API-Football
# Para estas ligas NO se sugiere "Sin Tarjeta Roja" porque la API no puede verificarlo
LIGAS_SIN_STATS = {
    "Uruguay Uruguay Primera División",
    "Uruguay Primera Division",
    "Peru Liga 1",
    "Bolivia Liga Profesional",
    "Ecuador Liga Pro",
    "Paraguay Division Profesional",
    "Venezuela Primera Division",
    "Baltic Cup",
    "Friendlies Clubs",
}

# ── MINI-TICKETS V15 ──────────────────────────────────────────────────────
# V15: EV positivo requiere cuota >= 1.19; objetivo 1.80-2.50 para EV real compuesto.
MINI_TICKET_CUOTA_MIN = 1.19       # V15: era 1.10
MINI_TICKET_CUOTA_MAX = 1.80
MINI_TICKET_CUOTA_OBJ_MIN = 1.80   # V15: era 1.40
MINI_TICKET_CUOTA_OBJ_MAX = 2.50   # V15: era 2.20
MINI_TICKET_PROB_MIN = 60.0        # V15: dinamico max(60, 103/cuota)
MINI_TICKET_MAX_DIA = 3            # V15: era 5 - selectividad radical
MINI_TICKET_MERCADOS = {"Doble oportunidad", "Goles totales", "Sin Tarjeta Roja"}


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
                    # V16: propagar campos de predictions al contexto de equipo
                    if team_key == "home":
                        ctx["home_scoring_rate_l5"] = ctx.get("home_scoring_rate_l5")
                        ctx["home_clean_sheet_l5"] = ctx.get("home_clean_sheet_l5")
                        ctx["home_goles_favor_l5"] = ctx.get("home_goles_favor_l5")
                    else:
                        ctx["away_scoring_rate_l5"] = ctx.get("away_scoring_rate_l5")
                        ctx["away_clean_sheet_l5"] = ctx.get("away_clean_sheet_l5")
                        ctx["away_goles_favor_l5"] = ctx.get("away_goles_favor_l5")
                    # V16: Acumular marcadores HT para first-half scoring rate
                    goles_ht = []
                    for _m in ultimos:
                        _ht = _m.get("score", {}).get("halftime", {})
                        _gf_ht = _ht.get("home") if _m["teams"]["home"]["id"] == team_id else _ht.get("away")
                        _gc_ht = _ht.get("away") if _m["teams"]["home"]["id"] == team_id else _ht.get("home")
                        if _gf_ht is not None:
                            goles_ht.append({"gf": _gf_ht or 0, "gc": _gc_ht or 0})
                    if goles_ht:
                        ctx[f"{team_key}_ht_scoring_rate"] = round(
                            sum(1 for g in goles_ht if g["gf"] > 0) / len(goles_ht), 3)
                        ctx[f"{team_key}_ht_goles_favor_prom"] = round(
                            sum(g["gf"] for g in goles_ht) / len(goles_ht), 2)
                        ctx[f"{team_key}_ht_concede_rate"] = round(
                            sum(1 for g in goles_ht if g["gc"] > 0) / len(goles_ht), 3)
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
                                # V16: campos adicionales de standings
                                ctx["home_goal_diff"] = team_st.get("goalsDiff")
                                ctx["home_forma_tabla"] = team_st.get("form")  # 'WWDLL'
                                ctx["home_descripcion"] = team_st.get("description")  # Relegation/Title
                                _h_home = team_st.get("home", {})
                                ctx["home_goles_favor_casa"] = _h_home.get("goals", {}).get("for")
                                ctx["home_goles_contra_casa"] = _h_home.get("goals", {}).get("against")
                                ctx["home_wins_casa"] = _h_home.get("win")
                                ctx["home_played_casa"] = _h_home.get("played")
                                _h_away = team_st.get("away", {})
                                ctx["home_goles_favor_visita"] = _h_away.get("goals", {}).get("for")
                                ctx["home_goles_contra_visita"] = _h_away.get("goals", {}).get("against")
                                ctx["home_wins_visita"] = _h_away.get("win")
                                ctx["home_played_visita"] = _h_away.get("played")
                            elif tid == away_id:
                                ctx["away_posicion"] = team_st.get("rank")
                                ctx["away_puntos"] = team_st.get("points")
                                ctx["away_partidos_jugados"] = team_st.get("all", {}).get("played")
                                # V16: campos adicionales de standings
                                ctx["away_goal_diff"] = team_st.get("goalsDiff")
                                ctx["away_forma_tabla"] = team_st.get("form")
                                ctx["away_descripcion"] = team_st.get("description")
                                _a_home = team_st.get("home", {})
                                ctx["away_goles_favor_casa"] = _a_home.get("goals", {}).get("for")
                                ctx["away_goles_contra_casa"] = _a_home.get("goals", {}).get("against")
                                _a_away = team_st.get("away", {})
                                ctx["away_goles_favor_visita"] = _a_away.get("goals", {}).get("for")
                                ctx["away_goles_contra_visita"] = _a_away.get("goals", {}).get("against")
                                ctx["away_wins_visita"] = _a_away.get("win")
                                ctx["away_played_visita"] = _a_away.get("played")
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
                # V16: Campos de /predictions sin usar hasta ahora
                ctx["api_under_over"] = p0.get("predictions", {}).get("under_over")  # '+2.5'/'-2.5'
                ctx["api_win_or_draw"] = p0.get("predictions", {}).get("win_or_draw")
                _cmp = p0.get("comparison", {})
                ctx["api_cmp_form_home"] = _cmp.get("form", {}).get("home")     # '60%'
                ctx["api_cmp_form_away"] = _cmp.get("form", {}).get("away")
                ctx["api_cmp_att_home"] = _cmp.get("att", {}).get("home")       # ataque relativo
                ctx["api_cmp_att_away"] = _cmp.get("att", {}).get("away")
                ctx["api_cmp_def_home"] = _cmp.get("def", {}).get("home")       # defensa relativa
                ctx["api_cmp_def_away"] = _cmp.get("def", {}).get("away")
                ctx["api_cmp_goals_home"] = _cmp.get("goals", {}).get("home")
                ctx["api_cmp_goals_away"] = _cmp.get("goals", {}).get("away")
                # last_5 de cada equipo: att = scoring rate, def_ = clean sheet rate
                _th = p0.get("teams", {}).get("home", {}).get("last_5", {})
                _ta = p0.get("teams", {}).get("away", {}).get("last_5", {})
                ctx["home_scoring_rate_l5"] = _th.get("att")     # '100%' = marcó en todos
                ctx["away_scoring_rate_l5"] = _ta.get("att")
                ctx["home_clean_sheet_l5"] = _th.get("def_")     # '60%' = no recibió en 60%
                ctx["away_clean_sheet_l5"] = _ta.get("def_")
                ctx["home_goles_favor_l5"] = _th.get("goals", {}).get("for", {}).get("average")
                ctx["away_goles_favor_l5"] = _ta.get("goals", {}).get("for", {}).get("average")
                ctx["home_goles_contra_l5"] = _th.get("goals", {}).get("against", {}).get("average")
                ctx["away_goles_contra_l5"] = _ta.get("goals", {}).get("against", {}).get("average")
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
        # Pick — valores originales Y recalibrados para ML
        "mercado": pick.get("mercado", ""),
        "jugada": pick.get("jugada", ""),
        "score": float(pick.get("score", 0) or 0),
        "score_original": float(pick.get("score_original", pick.get("score", 0)) or 0),
        "riesgo": float(pick.get("riesgo", 5) or 5),
        "probabilidad": float(pick.get("probabilidad", 0) or 0),
        "prob_original": float(pick.get("prob_original", pick.get("probabilidad", 0)) or 0),
        "cuota": float(pick.get("cuota", 1.0) or 1.0),
        "edge": pick.get("edge"),
        "valor_esperado": pick.get("valor_esperado"),
        # xG de predictions (si estuvo disponible)
        "xg_pred_home": pick.get("xg_pred_home"),
        "xg_pred_away": pick.get("xg_pred_away"),
        "xg_pred_total": pick.get("xg_pred_total"),
        "tipo": pick.get("tipo", "prematch"),
        "minuto_consulta": pick.get("minuto_consulta"),  # para picks live
        "resultado": resultado,
        "timestamp_aprendizaje": fecha_hora_peru(),
        # Variables enriquecidas (todas las que pudo obtener la API)
        **ctx,
    }
    # V15: Enriquecer con CLV si hay cuota de cierre disponible
    cuota_cierre = pick.get("cuota_cierre")
    if cuota_cierre:
        entrada = enriquecer_aprendizaje_clv(entrada, float(cuota_cierre))
    # V17: Registrar CLV timing score
    try:
        _hora_pick = pick.get("hora_generado")
        _hora_partido = pick.get("hora_partido")
        if _hora_pick and _hora_partido:
            from datetime import datetime as _dt_clv
            _dif_h = (_dt_clv.fromisoformat(_hora_partido) - _dt_clv.fromisoformat(_hora_pick)).seconds / 3600
            _clv_t = calcular_clv_timing_score(_dif_h, float(pick.get("cuota",1.5)))
            entrada["clv_timing"] = _clv_t["timing"]
            entrada["horas_antes"] = round(_dif_h, 1)
    except Exception:
        pass

    # V16: Acumular historial de árbitro
    try:
        _arb = ctx.get("arbitro") or pick.get("arbitro", "")
        if _arb and resultado in ("acierto", "fallo", "win", "loss", "W", "L"):
            _yh = int(ctx.get("home_yellow_cards", 0) or 0)
            _ya = int(ctx.get("away_yellow_cards", 0) or 0)
            _rh = int(ctx.get("home_red_cards", 0) or 0)
            _ra = int(ctx.get("away_red_cards", 0) or 0)
            if _yh + _ya > 0:
                actualizar_historial_arbitro(_arb, _yh, _ya, _rh, _ra,
                                             liga=ctx.get("liga_nombre", ""))
    except Exception:
        pass
    # V15: Guardar cuota de apertura si está disponible
    if pick.get("cuota_apertura"):
        entrada["cuota_apertura"] = pick["cuota_apertura"]
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

    cerrados = [d for d in datos if d.get("resultado") in ("acierto", "fallo", "push")]
    if len(cerrados) < 5:
        return {"insuficiente": True, "total": len(cerrados)}

    def efectividad_grupo(items):
        if not items:
            return 0.0
        # push no cuenta como acierto ni fallo para efectividad
        validos = [i for i in items if i.get("resultado") in ("acierto", "fallo")]
        if not validos:
            return 0.0
        ac = sum(1 for i in validos if i["resultado"] == "acierto")
        return round(ac / len(validos) * 100, 1)

    mercados = {}
    for d in cerrados:
        m = d.get("mercado") or d.get("jugada", "Otro")
        if "Corner" in m:
            m = "Corners"
        elif "goles" in m.lower() or "over" in m.lower() or "under" in m.lower():
            m = "Goles"
        elif "Tarjeta" in m:
            m = "Tarjetas"
        elif "BTTS" in m or "Ambos" in m:
            m = "BTTS"
        elif "Handicap" in m or "handicap" in m or "AH" in m:
            m = "Handicap"
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
    """Extrae la cuota de un pick de forma segura, tolerando None, 0 y strings.
    Orden: cuota_api (Pinnacle real) > cuota_pinnacle > cuota > cuota_minima."""
    for campo in ("cuota_api", "cuota_pinnacle", "cuota", "cuota_minima"):
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
    Recorre todas las operaciones cerradas del mes actual (picks individuales
    Y combinadas) y reconstruye el bank acumulado.
    Stake por pick individual: _stake_pct() segun score.
    Stake por combinada: STAKE_COMBINADA (10%).
    Se reinicia a BANK_INICIAL el primer dia de cada mes.
    """
    try:
        hoy = fecha_hoy_peru()
        mes_actual = hoy[:7]  # YYYY-MM

        bank = BANK_INICIAL
        historial = [{
            "fecha": f"{mes_actual}-01",
            "bank": bank,
            "operacion": f"inicio_mes_{mes_actual}",
            "nota": f"Reinicio mensual — S/ {BANK_INICIAL:.2f}"
        }]

        # Recopilar todas las operaciones del mes (picks + combinadas)
        operaciones = []

        # 1. Picks individuales cerrados del mes
        picks = leer_json(PICKS_FILE)
        for p in picks:
            estado = (p.get("estado") or p.get("resultado") or "").lower()
            if estado not in ("acierto", "fallo"):
                continue
            fecha_p = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
            if fecha_p[:7] != mes_actual:
                continue
            score = float(p.get("score", 0) or 0)
            riesgo = float(p.get("riesgo", 5) or 5)
            stake_pct = _stake_pct(score, riesgo)
            if stake_pct <= 0:
                continue  # pick no apto para simulacion de bank
            cuota = float(p.get("cuota_api") or p.get("cuota") or p.get("cuota_minima") or 1.5)
            cuota = min(max(cuota, 1.01), 10.0)  # limitar a rango razonable
            operaciones.append({
                "timestamp": p.get("timestamp", fecha_p),
                "fecha": fecha_p,
                "tipo": "pick",
                "ticket": p.get("fixture_id", ""),
                "subtipo": p.get("mercado", "pick"),
                "cuota": cuota,
                "stake_pct": stake_pct,
                "estado": estado,
                "partido": p.get("partido", ""),
            })

        # 2. Combinadas y mini-tickets cerrados del mes
        combinadas = leer_json(COMBINADAS_FILE)
        for c in combinadas:
            estado = (c.get("estado") or "").lower()
            if estado not in ("acierto", "fallo"):
                continue
            if c.get("sin_combinada"):
                continue
            fecha_c = (c.get("fecha") or "")[:10]
            if fecha_c[:7] != mes_actual:
                continue
            cuota = float(c.get("cuota_combinada", 1.0) or 1.0)
            cuota = min(max(cuota, 1.01), 50.0)
            # Mini-tickets usan stake fijo S/10, combinadas normales usan STAKE_COMBINADA
            if c.get("subtipo") == "MT":
                stake_pct_c = 10.0 / max(bank, 1.0)  # S/10 fijos
                stake_fijo = 10.0
            elif c.get("subtipo") == "DIA":
                stake_pct_c = STAKE_COMBINADA_DIA / max(bank, 1.0)
                stake_fijo = STAKE_COMBINADA_DIA
            else:
                stake_pct_c = STAKE_COMBINADA
                stake_fijo = None
            operaciones.append({
                "timestamp": c.get("timestamp", fecha_c),
                "fecha": fecha_c,
                "tipo": "combinada",
                "ticket": c.get("ticket_id", ""),
                "subtipo": c.get("subtipo", "combinada"),
                "cuota": cuota,
                "stake_pct": stake_pct_c,
                "stake_fijo": stake_fijo,
                "estado": estado,
            })

        # Ordenar por timestamp
        operaciones.sort(key=lambda x: x.get("timestamp", ""))

        for op in operaciones:
            stake_fijo = op.get("stake_fijo")
            if stake_fijo:
                stake = round(stake_fijo, 2)
            else:
                stake = round(bank * op["stake_pct"], 2)
            cuota = op["cuota"]
            estado = op["estado"]

            if estado == "acierto":
                ganancia = round(stake * (cuota - 1), 2)
                bank = round(bank + ganancia, 2)
                op_txt = f"+S/{ganancia:.2f}"
            else:
                bank = round(bank - stake, 2)
                op_txt = f"-S/{stake:.2f}"

            historial.append({
                "fecha": op["fecha"],
                "ticket": op["ticket"],
                "tipo": op["tipo"],
                "subtipo": op["subtipo"],
                "cuota": cuota,
                "stake": stake,
                "estado": estado,
                "operacion": op_txt,
                "bank": bank,
                "mes": mes_actual,
                "partido": op.get("partido", ""),
            })

        _guardar_bank_acumulado(historial)
        return historial
    except Exception as e:
        print(f"ERROR _actualizar_bank_acumulado: {e}")
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


def _son_compatibles(jugada1, jugada2):
    """
    Valida que dos mercados del mismo partido no se contradigan.
    Retorna True si son compatibles (correlacion positiva o neutra).
    Retorna False si se contradicen (no deben ir juntos en un ticket).
    """
    j1 = jugada1.lower()
    j2 = jugada2.lower()

    # Contradicciones directas — nunca juntas
    if "over 2.5" in j1 and "under 2.5" in j2: return False
    if "under 2.5" in j1 and "over 2.5" in j2: return False
    if "over 3.5" in j1 and "under 3.5" in j2: return False
    if "under 3.5" in j1 and "over 3.5" in j2: return False
    if "over 1.5" in j1 and "under 1.5" in j2: return False
    if "under 1.5" in j1 and "over 1.5" in j2: return False
    if "1x" in j1 and "x2" in j2: return False
    if "x2" in j1 and "1x" in j2: return False

    # Contradicciones logicas — partidos con muchos goles vs sin roja
    # Over 2.5 + Sin Roja: tension alta con muchos goles es contradictorio
    if "over 2.5" in j1 and "sin tarjeta roja" in j2: return False
    if "sin tarjeta roja" in j1 and "over 2.5" in j2: return False

    # Over 1.5 y Sin Roja: aceptable — puede haber goles sin tension
    # Under 3.5 + Sin Roja: correlacion positiva (partido tranquilo)
    # 1X/X2 + Sin Roja: correlacion positiva
    # Doble op + Goles: correlacion positiva en general

    return True


def _armar_combinada_dia_garantizada():
    """
    Combinada garantizada del dia — criterios mas flexibles que _armar_combinada_del_dia:
    - Cuota individual minima: 1.25 (vs 1.50 del sistema normal)
    - Score minimo: 7.5 (vs 8.0)
    - Cuota total objetivo: 2.0-3.5
    - 3 eslabones de partidos DISTINTOS
    - Mercados: Goles, Doble Oportunidad (no BTTS)
    - Stake fijo: STAKE_COMBINADA_DIA (S/25)
    """
    from itertools import combinations as _comb_g
    import uuid as _uuid_g

    picks = leer_json(PICKS_FILE)
    hoy = fecha_hoy_peru()
    ahora_str = fecha_peru_obj().strftime("%H:%M")

    # Candidatos: picks prematch pendientes de hoy con cuota >= 1.25
    candidatos = []
    for p in picks:
        fecha_pick = (p.get("fecha_partido") or p.get("fecha") or "")[:10]
        if fecha_pick != hoy:
            continue
        if p.get("tipo", "") != "prematch":
            continue
        if p.get("estado", "pendiente").lower() not in ("pendiente", "pendiente_manual"):
            continue
        if _es_btts(p):
            continue

        cuota = _cuota_segura(p)
        if cuota < 1.25:  # mas permisivo que el sistema normal (1.50)
            continue

        score = float(p.get("score", 0) or 0)
        if score < 7.5:
            continue

        # Verificar partido aun no empezado
        hora_pick = p.get("hora", p.get("hour", ""))
        if hora_pick and hora_pick <= ahora_str:
            continue

        candidatos.append(p)

    # Si no hay suficientes en picks_guardados, analizar partidos del dia
    if len(candidatos) < 3:
        ligas = {}
        ligas.update(EUROPA_LEAGUES)
        ligas.update(SUDAMERICA_LEAGUES)
        ligas.update(OTRAS_LEAGUES)
        ligas.update(SELECCIONES_LEAGUES)
        partidos_dia = obtener_fixtures_por_fecha(ligas, hoy)
        ahora_ts = int(fecha_peru_obj().timestamp())

        for p_dia in partidos_dia:
            if int(p_dia.get("timestamp", 0)) <= ahora_ts + 1800:
                continue
            fid = str(p_dia["id"])
            if any(str(c.get("fixture_id","")) == fid for c in candidatos):
                continue
            try:
                data = preparar_analisis(fid, incluir_odds=True, incluir_contexto=False)
                if not data or not data["recomendaciones"]:
                    continue
                top = data["recomendaciones"][0]
                cuota_t = _cuota_segura(top)
                score_t = float(top.get("score", 0) or 0)
                if cuota_t >= 1.25 and score_t >= 7.5 and not _es_btts(top):
                    candidato = {
                        "fixture_id": fid,
                        "partido": f"{data['home']} vs {data['away']}",
                        "league": data["league"],
                        "country": data.get("country", ""),
                        "hora": data["hora"],
                        "tipo": "prematch",
                        **top,
                    }
                    candidatos.append(candidato)
            except Exception:
                continue

    if len(candidatos) < 2:
        return {
            "sin_combinada": True,
            "fecha": hoy,
            "motivo": f"Solo {len(candidatos)} picks validos (minimo 2 para combinada garantizada)"
        }

    candidatos.sort(key=lambda x: float(x.get("score", 0) or 0), reverse=True)

    mejor = None
    mejor_valor = -999
    n_objetivo = 3 if len(candidatos) >= 3 else 2

    for n in ([n_objetivo, n_objetivo - 1] if n_objetivo > 2 else [2]):
        if len(candidatos) < n:
            continue
        for grupo in _comb_g(candidatos, n):
            grupo = list(grupo)
            # Solo partidos distintos
            fids_g = [str(p.get("fixture_id","")) for p in grupo]
            if len(set(fids_g)) < len(fids_g):
                continue
            cuota_g = 1.0
            for p in grupo:
                cuota_g *= max(_cuota_segura(p), 1.0)
            cuota_g = round(cuota_g, 2)
            if cuota_g < 2.0 or cuota_g > 3.5:
                continue
            # VE
            prob_g = 1.0
            for p in grupo:
                prob_g *= (_prob_recalibrada_pick(p) / 100.0)
            ve = prob_g * (cuota_g - 1.0) - (1.0 - prob_g)
            if ve > mejor_valor:
                mejor_valor = ve
                mejor = grupo

    if not mejor:
        return {
            "sin_combinada": True,
            "fecha": hoy,
            "motivo": f"Ninguna combinacion con cuota 2.0-3.5 entre {len(candidatos)} candidatos"
        }

    cuota_final = round(
        sum(_cuota_segura(p) for p in mejor) / len(mejor), 2
    )
    cuota_final = 1.0
    for p in mejor:
        cuota_final *= max(_cuota_segura(p), 1.0)
    cuota_final = round(cuota_final, 2)

    uid = str(_uuid_g.uuid4())[:6].upper()
    ticket_id = f"COMB-DIA-{hoy.replace('-','')[2:]}-{uid}"

    return {
        "ticket_id": ticket_id,
        "tipo": "combinada_dia",
        "subtipo": "DIA",
        "fecha": hoy,
        "picks": mejor,
        "n_picks": len(mejor),
        "cuota_combinada": cuota_final,
        "stake_fijo": STAKE_COMBINADA_DIA,
        "score_promedio": round(
            sum(float(p.get("score",0) or 0) for p in mejor) / len(mejor), 1
        ),
        "riesgo_promedio": round(
            sum(float(p.get("riesgo",5) or 5) for p in mejor) / len(mejor), 1
        ),
        "estado": "pendiente",
        "razon_seleccion": f"Combinada garantizada — cuota {cuota_final}x | VE={round(mejor_valor,3)}",
        "timestamp": fecha_hora_peru(),
    }


def _extraer_cuota_handicap_pinnacle(odds, equipo, linea):
    """
    Extrae la cuota real de Asian Handicap de Pinnacle.
    equipo: 'home' o 'away'
    linea: -0.5, -0.25, -0.75, 0, +0.5, etc.
    Devuelve (cuota, bookmaker) o (None, None) si no hay.
    """
    PINNACLE_NAMES = {"Pinnacle", "Pinnacle Sports"}
    AH_MARKETS = {"Asian Handicap", "Asian handicap", "Handicap Asiatico",
                  "Handicap Asian", "AH", "Asian"}
    linea_str_variants = [
        f"{linea:+.1f}", f"{linea:+.2f}",
        f"{linea:.1f}", f"{linea:.2f}",
        str(linea),
    ]
    equipo_label = "Home" if equipo == "home" else "Away"

    for casa in odds:
        for book in casa.get("bookmakers", []):
            if book.get("name", "") not in PINNACLE_NAMES:
                continue
            for bet in book.get("bets", []):
                bet_name = bet.get("name", "")
                if not any(ah.lower() in bet_name.lower() for ah in AH_MARKETS):
                    continue
                for value in bet.get("values", []):
                    nombre = str(value.get("value", ""))
                    # nombre puede ser "Home -0.5", "Away +0.5", "-0.5", etc.
                    coincide_equipo = equipo_label.lower() in nombre.lower()
                    coincide_linea = any(v in nombre for v in linea_str_variants)
                    if coincide_equipo and coincide_linea:
                        try:
                            cuota = float(value.get("odd"))
                            if cuota > 1.0:
                                return round(cuota, 3), "Pinnacle"
                        except Exception:
                            pass
    return None, None


def calcular_handicap_recomendado_club(home_general, away_general,
                                        home_home, away_away, odds):
    """
    Calcula el handicap asiatico recomendado para un partido de clubes.
    Usa gf_prom, gc_prom y forma de calcular_forma.
    Solo recomienda si hay cuota real de Pinnacle >= HANDICAP_CUOTA_MIN.
    Devuelve dict con jugada, equipo, linea, cuota, prob_estimada o None.
    """
    base_home = home_home or home_general
    base_away = away_away or away_general

    if not base_home or not base_away:
        return None

    gf_home = float(base_home.get("gf_prom", 0) or 0)
    gc_home = float(base_home.get("gc_prom", 0) or 0)
    gf_away = float(base_away.get("gf_prom", 0) or 0)
    gc_away = float(base_away.get("gc_prom", 0) or 0)

    # V16: Usar split home/away si disponible (más preciso que promedio total)
    # El split viene de standings: goles solo en partidos de casa o solo de visita
    _gf_home_split = base_home.get("gf_casa")   # goles/pto del local SOLO en casa
    _gf_away_split = base_away.get("gf_visita")  # goles/pto del visitante SOLO de visita
    _gc_home_split = base_home.get("gc_casa")
    _gc_away_split = base_away.get("gc_visita")
    if _gf_home_split and float(_gf_home_split) > 0:
        gf_home = float(_gf_home_split)
    if _gf_away_split and float(_gf_away_split) > 0:
        gf_away = float(_gf_away_split)
    if _gc_home_split and float(_gc_home_split) > 0:
        gc_home = float(_gc_home_split)
    if _gc_away_split and float(_gc_away_split) > 0:
        gc_away = float(_gc_away_split)

    # N2: xGA proxy desde shots si no hay xGA directo
    _shots_home = float(base_home.get("shots_on_goal", 0) or 0)
    _shots_away = float(base_away.get("shots_on_goal", 0) or 0)
    _xga_home_proxy = calcular_xga_proxy(_shots_away) if _shots_away > 0 else gc_home
    _xga_away_proxy = calcular_xga_proxy(_shots_home) if _shots_home > 0 else gc_away

    # X8: Set piece rate flag
    _spr_home = flag_set_piece_rate(gf_home, _shots_home)
    _spr_away = flag_set_piece_rate(gf_away, _shots_away)
    _xg_spr_adj_home = _spr_home["ajuste_xg"]
    _xg_spr_adj_away = _spr_away["ajuste_xg"]

    # Z14: Home/away split — usar xG contextual por rol
    _gf_home_en_casa = float(base_home.get("gf_home", gf_home) or gf_home)
    _gf_away_de_visita = float(base_away.get("gf_away", gf_away) or gf_away)
    _split_home = ajuste_ah_home_away_split(_gf_home_en_casa, base_home.get("gf_away", gf_home * 0.8), es_local=True)
    _split_away = ajuste_ah_home_away_split(base_away.get("gf_home", gf_away * 1.1), _gf_away_de_visita, es_local=False)
    # Usar xG contextual para la tabla AH
    _xg_home_contextual = _split_home["xg_contextual"]
    _xg_away_contextual = _split_away["xg_contextual"]

    # Fuerza atacante vs defensiva
    ataque_home = gf_home - gc_away   # positivo = local domina
    ataque_away = gf_away - gc_home   # positivo = visitante domina
    diferencia = ataque_home - ataque_away

    # V15 Z11-Z14: Usar tabla AH basada en diff xG en lugar de rangos fijos
    _xg_home_est = max(0.3, gf_home * 0.7 + gc_away * 0.3)
    _xg_away_est = max(0.2, gf_away * 0.6 + gc_home * 0.4)
    _efic_home = float(base_home.get("eficiencia_ofensiva", 1.0) or 1.0)
    _ah_rec = recomendar_linea_ah(_xg_home_est, _xg_away_est, _efic_home)
    _linea_txt = _ah_rec["linea"]
    # AH2/Z12: Ajustar línea por eficiencia ofensiva del favorito
    if _efic_home < 0.80 or _efic_home > 1.20:
        _linea_txt = ajustar_linea_ah_por_eficiencia(_linea_txt, _efic_home)

    # Mapear linea textual a valor numerico
    _linea_map = {
        "AH(0)": 0.0, "AH(-0.25)": -0.25, "AH(-0.5)": -0.5,
        "AH(-0.75)": -0.75, "AH(-1.0)": -1.0, "AH(-1.25)": -1.25,
        "AH(-1.5)+": -1.5, "AH(+0.25)": 0.25, "AH(+0.5)": 0.5,
        "AH(+0.75)+": 0.75,
    }
    _linea_num = _linea_map.get(_linea_txt, None)

    # Decidir equipo y linea con la tabla V15
    if diferencia > 0 and _linea_num is not None and _linea_num <= -0.25:
        equipo = "home"
        linea = _linea_num
        prob_est = {-0.25: 68.0, -0.5: 62.0, -0.75: 58.0,
                    -1.0: 56.0, -1.25: 55.0, -1.5: 54.0}.get(linea, 60.0)
    elif diferencia < 0 and _linea_num is not None and _linea_num >= 0.25:
        equipo = "away"
        linea = -abs(_linea_num)  # linea AH del visitante
        prob_est = {-0.25: 68.0, -0.5: 62.0, -0.75: 58.0}.get(linea, 60.0)
    elif abs(diferencia) < 0.5:
        return None  # partido muy parejo, no recomendar
    # Fallback al sistema original si la tabla no da resultado claro
    elif diferencia >= 1.5:
        equipo, linea = "home", -0.75
        prob_est = 58.0
    elif diferencia >= 0.8:
        equipo, linea = "home", -0.5
        prob_est = 62.0
    elif diferencia >= 0.5:
        equipo, linea = "home", -0.25
        prob_est = 68.0
    elif diferencia <= -1.5:
        equipo, linea = "away", -0.75
        prob_est = 58.0
    elif diferencia <= -0.8:
        equipo, linea = "away", -0.5
        prob_est = 62.0
    elif diferencia <= -0.5:
        equipo, linea = "away", -0.25
        prob_est = 68.0
    else:
        return None  # partido muy parejo, no recomendar

    # V14.3: Filtro de forma reciente — no recomendar handicap si el equipo
    # favorito lleva 3+ partidos sin ganar (forma negativa reciente)
    base_fav = base_home if equipo == "home" else base_away
    forma_reciente = (base_fav or {}).get("forma", "")[:3]  # últimos 3 partidos
    if forma_reciente and forma_reciente.count("L") >= 2:
        return None  # Mal momento — forma reciente descarta el pick

    # Buscar cuota real de Pinnacle — Opcion B: solo con cuota real
    cuota, book = _extraer_cuota_handicap_pinnacle(odds, equipo, linea)
    if not cuota or cuota < HANDICAP_CUOTA_MIN:
        return None  # sin cuota real o cuota insuficiente

    return {
        "equipo": equipo,
        "linea": linea,
        "cuota": cuota,
        "bookmaker": book,
        "prob_estimada": prob_est,
        "diferencia_fuerza": round(diferencia, 2),
    }


def calcular_handicap_recomendado_seleccion(home, away, odds):
    """
    Calcula el handicap recomendado para selecciones usando ranking FIFA.
    Solo recomienda si hay cuota real de Pinnacle >= HANDICAP_CUOTA_MIN.
    """
    rank_home = RANKING_FIFA.get(home, 60)
    rank_away = RANKING_FIFA.get(away, 60)
    diff_ranking = rank_away - rank_home  # positivo = local mejor rankeado

    if diff_ranking >= 30:
        equipo, linea = "home", -0.75
        prob_est = 58.0   # V14.3: subido de 52% — -0.75 selecciones requiere diferencia clara
    elif diff_ranking >= 15:
        equipo, linea = "home", -0.5
        prob_est = 60.0
    elif diff_ranking >= 7:
        equipo, linea = "home", -0.25
        prob_est = 66.0
    elif diff_ranking <= -30:
        equipo, linea = "away", -0.75
        prob_est = 58.0
    elif diff_ranking <= -15:
        equipo, linea = "away", -0.5
        prob_est = 60.0
    elif diff_ranking <= -7:
        equipo, linea = "away", -0.25
        prob_est = 66.0
    else:
        return None  # selecciones muy parejas, no recomendar

    cuota, book = _extraer_cuota_handicap_pinnacle(odds, equipo, linea)
    if not cuota or cuota < HANDICAP_CUOTA_MIN:
        return None

    return {
        "equipo": equipo,
        "linea": linea,
        "cuota": cuota,
        "bookmaker": book,
        "prob_estimada": prob_est,
        "diff_ranking": diff_ranking,
    }


def guardar_handicap(registro):
    """
    Guarda un pick de handicap en HANDICAP_FILE.
    Evita duplicados por (fixture_id, equipo, linea).
    """
    data = leer_json(HANDICAP_FILE)
    fid = str(registro.get("fixture_id", ""))
    eq = registro.get("equipo", "")
    ln = registro.get("linea", 0)

    for r in data:
        if (str(r.get("fixture_id","")) == fid
                and r.get("equipo") == eq
                and r.get("linea") == ln):
            return False  # duplicado

    data.append(registro)
    guardar_json_lista(HANDICAP_FILE, data)
    return True


def filtrar_handicaps_por_dias(dias):
    """Lee handicap_seguimiento.json y filtra por los ultimos N dias."""
    cerrar_handicaps_pendientes()
    data = leer_json(HANDICAP_FILE)
    hoy = fecha_peru_obj()
    limite = hoy - timedelta(days=dias)
    filtrados = []
    for r in data:
        try:
            fp = datetime.strptime(r.get("fecha","")[:10], "%Y-%m-%d")
            if fp >= limite:
                filtrados.append(r)
        except Exception:
            continue
    return filtrados


def filtrar_handicaps_mes_actual():
    """Lee handicap_seguimiento.json y filtra por el mes actual."""
    cerrar_handicaps_pendientes()
    data = leer_json(HANDICAP_FILE)
    hoy = fecha_peru_obj()
    filtrados = []
    for r in data:
        try:
            fp = datetime.strptime(r.get("fecha","")[:10], "%Y-%m-%d")
            if fp.year == hoy.year and fp.month == hoy.month:
                filtrados.append(r)
        except Exception:
            continue
    return filtrados


def cerrar_handicaps_pendientes():
    """
    Cierra automaticamente los picks de handicap pendientes.
    Logica de cierre:
      -0.5 / +0.5 : gana por 1+ -> acierto | empate/pierde -> fallo
      -0.25       : gana por 1+ -> acierto | empate -> push | pierde -> fallo
      -0.75       : gana por 2+ -> acierto | gana por 1 -> push | empata/pierde -> fallo
      0           : gana -> acierto | empate -> push | pierde -> fallo
    Registra resultado en aprendizaje.json.
    """
    data = leer_json(HANDICAP_FILE)
    cambios = 0

    for r in data:
        if r.get("estado", "pendiente") not in ("pendiente",):
            continue
        fixture_id = r.get("fixture_id")
        if not fixture_id:
            continue
        try:
            fixture = api_get(f"/fixtures?id={fixture_id}", use_cache=False)
        except Exception:
            continue
        if not fixture:
            continue
        fx = fixture[0]
        status = fx["fixture"]["status"]["short"]
        if status not in ("FT", "AET", "PEN"):
            continue

        gh = fx["goals"]["home"]
        ga = fx["goals"]["away"]
        if gh is None or ga is None:
            continue

        equipo = r.get("equipo", "home")
        linea = float(r.get("linea", -0.5))

        # Diferencia de goles desde perspectiva del equipo apostado
        if equipo == "home":
            diff = gh - ga
        else:
            diff = ga - gh

        # Aplicar linea al diff
        diff_ajustado = diff + linea

        resultado = None
        retorno = 0.0
        cuota = float(r.get("cuota", 1.90) or 1.90)

        if linea in (-0.5, 0.5, -1.0, 1.0, -1.5, 1.5):
            # Linea entera: acierto o fallo
            if diff_ajustado > 0:
                resultado = "acierto"
                retorno = round(cuota - 1, 3)
            else:
                resultado = "fallo"
                retorno = -1.0

        elif linea in (-0.25, 0.25, -1.25, 1.25):
            # Linea cuarto: puede ser push parcial
            if diff_ajustado > 0:
                resultado = "acierto"
                retorno = round(cuota - 1, 3)
            elif diff_ajustado == 0:
                # Si la linea es -0.25 y diff exacto es 0: push 50%
                resultado = "push"
                retorno = 0.0
            else:
                resultado = "fallo"
                retorno = -1.0

        elif linea in (-0.75, 0.75, -1.75, 1.75):
            if diff_ajustado > 0:
                resultado = "acierto"
                retorno = round(cuota - 1, 3)
            elif diff_ajustado == 0:
                # gana por exactamente 1 con -0.75: push 50%
                resultado = "push"
                retorno = 0.0
            else:
                resultado = "fallo"
                retorno = -1.0

        elif linea == 0:
            if diff > 0:
                resultado = "acierto"
                retorno = round(cuota - 1, 3)
            elif diff == 0:
                resultado = "push"
                retorno = 0.0
            else:
                resultado = "fallo"
                retorno = -1.0

        else:
            # Otras lineas: simplificar como entera
            if diff_ajustado > 0:
                resultado = "acierto"
                retorno = round(cuota - 1, 3)
            else:
                resultado = "fallo"
                retorno = -1.0

        if resultado:
            r["estado"] = resultado
            r["resultado"] = resultado
            r["retorno"] = retorno
            r["gh"] = gh
            r["ga"] = ga
            r["resultado_real"] = f"{gh}-{ga}"
            cambios += 1

            # Registrar en aprendizaje.json para ML futuro
            try:
                ctx = {}
                try:
                    ctx = _enriquecer_contexto_pick(
                        fixture_id,
                        r.get("league_id"),
                        r.get("season")
                    )
                except Exception:
                    pass
                entrada_ap = {
                    "fecha": r.get("fecha", "")[:10],
                    "fixture_id": fixture_id,
                    "partido": r.get("partido", ""),
                    "liga": r.get("league", ""),
                    "pais": r.get("country", ""),
                    "mercado": "Handicap Asiatico",
                    "jugada": r.get("jugada", ""),
                    "equipo": r.get("equipo", ""),
                    "linea": r.get("linea"),
                    "cuota": cuota,
                    "prob_estimada": r.get("prob_estimada", 0),
                    "tipo_equipo": r.get("tipo_equipo", "club"),
                    "resultado": resultado,
                    "retorno": retorno,
                    "gh": gh,
                    "ga": ga,
                    "modo": "observacion",
                    "timestamp_aprendizaje": fecha_hora_peru(),
                    **ctx,
                }
                agregar_json(APRENDIZAJE_FILE, entrada_ap)
            except Exception as e:
                print(f"WARN aprendizaje handicap: {e}")

    if cambios > 0:
        guardar_json_lista(HANDICAP_FILE, data)
        print(f"[handicap] {cambios} picks cerrados")

    return cambios


def _seccion_handicap_pdf(c, y, hoy):
    """Agrega seccion de handicap al PDF del resumen diario."""
    try:
        data = leer_json(HANDICAP_FILE)
        hoy_picks = [r for r in data if r.get("fecha","")[:10] == hoy]
        if not hoy_picks:
            return y

        y -= 10
        c.setFont("Helvetica-Bold", 11)
        c.drawString(40, y, f"HANDICAP ASIATICO — MODO OBSERVACION ({len(hoy_picks)} picks)")
        y -= 16
        c.setFont("Helvetica", 9)

        cerrados_h = [r for r in hoy_picks if r.get("estado") in ("acierto","fallo","push")]
        if cerrados_h:
            aciertos_h = sum(1 for r in cerrados_h if r.get("estado") == "acierto")
            fallos_h = sum(1 for r in cerrados_h if r.get("estado") == "fallo")
            push_h = sum(1 for r in cerrados_h if r.get("estado") == "push")
            validos_h = aciertos_h + fallos_h
            ef_h = round(aciertos_h / validos_h * 100, 1) if validos_h else 0
            c.drawString(40, y, f"Cerrados: {len(cerrados_h)} | Aciertos: {aciertos_h} | Fallos: {fallos_h} | Push: {push_h} | Efectividad: {ef_h}%")
            y -= 12

        for r in hoy_picks:
            estado = r.get("estado","pendiente").upper()
            jugada = r.get("jugada","")
            cuota = r.get("cuota","?")
            resultado_real = r.get("resultado_real","")
            linea = f"  • {r.get('partido','')} | {jugada} | {cuota}x | {estado}"
            if resultado_real:
                linea += f" | {resultado_real}"
            c.drawString(40, y, linea[:110])
            y -= 11
            if y < 60:
                c.showPage()
                y = 780
                c.setFont("Helvetica", 9)
    except Exception as e:
        print(f"WARN _seccion_handicap_pdf: {e}")
    return y


def _seccion_handicap_historico_pdf(elements, fecha_inicio, fecha_fin, styles):
    """Agrega resumen historico de handicap al PDF semanal/mensual."""
    try:
        data = leer_json(HANDICAP_FILE)
        periodo = [r for r in data
                   if fecha_inicio <= r.get("fecha","")[:10] <= fecha_fin]
        if not periodo:
            return

        cerrados = [r for r in periodo if r.get("estado") in ("acierto","fallo","push")]
        if not cerrados:
            return

        aciertos = sum(1 for r in cerrados if r.get("estado") == "acierto")
        fallos = sum(1 for r in cerrados if r.get("estado") == "fallo")
        push = sum(1 for r in cerrados if r.get("estado") == "push")
        validos = aciertos + fallos
        ef = round(aciertos / validos * 100, 1) if validos else 0
        roi_sim = sum(r.get("retorno", 0) for r in cerrados)

        s_h2 = styles["Heading2"].clone("hh2")
        s_h2.fontSize = 11
        s_h2.spaceBefore = 10
        elements.append(Paragraph("Handicap Asiatico — Modo Observacion", s_h2))
        elements.append(Spacer(1, 4))

        resumen_txt = (
            f"Total picks: {len(periodo)} | Cerrados: {len(cerrados)} | "
            f"Aciertos: {aciertos} | Fallos: {fallos} | Push: {push} | "
            f"Efectividad: {ef}% | ROI simulado: {roi_sim:+.2f}u"
        )
        elements.append(Paragraph(resumen_txt, styles["Normal"]))
        elements.append(Spacer(1, 6))

        # Por tipo de linea
        por_linea = {}
        for r in cerrados:
            ln = str(r.get("linea", "?"))
            por_linea.setdefault(ln, {"ok": 0, "fallo": 0, "push": 0})
            est = r.get("estado","")
            if est == "acierto": por_linea[ln]["ok"] += 1
            elif est == "fallo": por_linea[ln]["fallo"] += 1
            elif est == "push": por_linea[ln]["push"] += 1

        for ln, v in sorted(por_linea.items()):
            tot = v["ok"] + v["fallo"]
            ef_ln = round(v["ok"] / tot * 100, 1) if tot else 0
            elements.append(Paragraph(
                f"  Linea {ln}: {v['ok']}A / {v['fallo']}F / {v['push']}P — {ef_ln}%",
                styles["Normal"]
            ))
    except Exception as e:
        print(f"WARN _seccion_handicap_historico_pdf: {e}")


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
            # G: Verificar que todos sean partidos DISTINTOS (no correlacionados)
            ids_grupo = [str(p.get("fixture_id", "")) for p in grupo]
            if len(set(ids_grupo)) < len(ids_grupo):
                continue
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


def generar_mini_tickets_dia():
    """
    Genera los mejores mini-tickets del dia.
    Cada ticket tiene 2-3 eslabones con cuota individual 1.10-1.60.
    Mercados: Doble Oportunidad, Goles (Over/Under segun partido), Sin Tarjeta Roja.
    Cuota total objetivo: 1.40-2.20.
    Probabilidad conjunta minima: 62%.
    Maximo MINI_TICKET_MAX_DIA tickets por dia.
    Puede mezclar partidos diferentes o usar maximo 2 mercados del mismo partido
    si son compatibles (correlacion positiva).
    """
    from itertools import combinations as _comb_mt
    import uuid as _uuid_mt

    hoy = fecha_hoy_peru()
    ahora_ts = int(fecha_peru_obj().timestamp())

    # Recopilar todos los partidos de hoy que aun no empiezan
    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)
    ligas.update(SELECCIONES_LEAGUES)

    partidos_dia = obtener_fixtures_por_fecha(ligas, hoy)

    # Filtrar solo partidos que empiezan en mas de 30 minutos
    partidos_validos = []
    for p in partidos_dia:
        ts = p.get("timestamp", 0)
        if ts - ahora_ts > 1800:  # 30 minutos
            partidos_validos.append(p)

    if not partidos_validos:
        return []

    # Generar eslabones candidatos para cada partido
    eslabones = []
    picks_ya_usados = set()  # (fixture_id, jugada) para evitar duplicar

    for p in partidos_validos:
        fixture_id = str(p["id"])
        try:
            data = preparar_analisis(
                fixture_id,
                incluir_odds=True,
                incluir_contexto=True
            )
            if not data:
                continue

            home_gen = data.get("home_general") or {}
            away_gen = data.get("away_general") or {}
            home_hh = data.get("home_home") or home_gen
            away_aa = data.get("away_away") or away_gen

            if not home_gen or not away_gen:
                continue

            home = data["home"]
            away = data["away"]
            hora = data["hora"]
            league = data["league"]
            country = data.get("country", "")

            # Obtener odds directamente para cuotas reales
            odds_mt = api_get(f"/odds?fixture={fixture_id}", use_cache=True, ttl=600)

            # ── PUNTO 2: H2H como filtro de descarte para Under ──────────
            # Calcular promedio H2H del partido específico
            try:
                h2h_mt = api_get(
                    f"/fixtures/headtohead?h2h={p.get('home_id','')}-{p.get('away_id','')}&last=5",
                    use_cache=True, ttl=7200
                )
                if not h2h_mt:
                    # Intentar obtener IDs desde fixture
                    fx_ids = api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)
                    if fx_ids:
                        hid = fx_ids[0]["teams"]["home"]["id"]
                        aid = fx_ids[0]["teams"]["away"]["id"]
                        h2h_mt = api_get(f"/fixtures/headtohead?h2h={hid}-{aid}&last=5",
                                        use_cache=True, ttl=7200)
                goles_h2h_mt = [
                    (m["goals"]["home"] or 0) + (m["goals"]["away"] or 0)
                    for m in (h2h_mt or [])
                    if m["goals"]["home"] is not None
                ]
                prom_h2h_mt = sum(goles_h2h_mt) / len(goles_h2h_mt) if goles_h2h_mt else None
            except Exception:
                prom_h2h_mt = None

            # ── PUNTO 8: Usar score real de preparar_analisis ────────────
            # Obtener el score más alto de las recomendaciones del partido
            recs_data = data.get("recomendaciones", [])
            score_partido = max(
                (float(r.get("score", 7.5) or 7.5) for r in recs_data),
                default=7.5
            )
            # Mapa jugada → score real calculado por preparar_analisis
            score_por_jugada = {
                r.get("jugada", ""): float(r.get("score", 7.5) or 7.5)
                for r in recs_data
            }
            # xG del partido si está disponible
            xg_total_mt = None
            for r in recs_data:
                if r.get("xg_pred_total"):
                    xg_total_mt = float(r["xg_pred_total"])
                    break

            base_home = home_hh or home_gen
            base_away = away_aa or away_gen
            total_prom = (base_home.get("total_prom", 0) + base_away.get("total_prom", 0)) / 2
            under35 = (base_home.get("under35", 0) + base_away.get("under35", 0)) / 2
            over15 = (base_home.get("over15", 0) + base_away.get("over15", 0)) / 2
            over25 = (base_home.get("over25", 0) + base_away.get("over25", 0)) / 2
            under25 = 1 - over25  # aproximación

            # ── PUNTO 5: Recalibrar probs individuales ───────────────────
            def _prob_mt(prob_raw):
                """Recalibra prob para evitar valores irreales (máx 88%)."""
                return min(88.0, recalibrar_probabilidad(float(prob_raw or 0)))

            # 1. Under 3.5 — con filtro H2H y score real
            if under35 >= 0.65:
                prob_u35 = _prob_mt(under35 * 100)
                # Punto 2: descartar si H2H promedio supera la línea
                if prom_h2h_mt is not None and prom_h2h_mt >= 3.5:
                    pass  # contradictorio con H2H
                elif xg_total_mt is not None and xg_total_mt > 3.5:
                    pass  # xG también contradice Under 3.5
                elif prob_u35 >= 60:
                    cuota_u35, _ = buscar_mejor_cuota(fixture_id, "Under 3.5 goles")
                    if cuota_u35 and MINI_TICKET_CUOTA_MIN <= cuota_u35 <= MINI_TICKET_CUOTA_MAX:
                        clave = (fixture_id, "Under 3.5 goles")
                        if clave not in picks_ya_usados:
                            picks_ya_usados.add(clave)
                            score_u35 = score_por_jugada.get("Under 3.5 goles", score_partido)
                            eslabones.append({
                                "fixture_id": fixture_id,
                                "partido": f"{home} vs {away}",
                                "home": home, "away": away,
                                "league": league, "country": country,
                                "hora": hora,
                                "mercado": "Goles totales",
                                "jugada": "Under 3.5 goles",
                                "prob": prob_u35,
                                "cuota": cuota_u35,
                                "score": round(score_u35, 1),
                                "fecha": hoy,
                            })

            # 2. Over 1.5 — con filtro H2H y score real
            if over15 >= 0.70:
                prob_o15 = _prob_mt(over15 * 100)
                # Descartar si H2H promedio es muy bajo (partidos cerrados)
                if prom_h2h_mt is not None and prom_h2h_mt < 1.0:
                    pass  # H2H sugiere partidos 0-0 o 1-0
                elif prob_o15 >= 65:
                    cuota_o15, _ = buscar_mejor_cuota(fixture_id, "Over 1.5 goles")
                    if cuota_o15 and MINI_TICKET_CUOTA_MIN <= cuota_o15 <= MINI_TICKET_CUOTA_MAX:
                        clave = (fixture_id, "Over 1.5 goles")
                        if clave not in picks_ya_usados:
                            picks_ya_usados.add(clave)
                            score_o15 = score_por_jugada.get("Over 1.5 goles", score_partido)
                            eslabones.append({
                                "fixture_id": fixture_id,
                                "partido": f"{home} vs {away}",
                                "home": home, "away": away,
                                "league": league, "country": country,
                                "hora": hora,
                                "mercado": "Goles totales",
                                "jugada": "Over 1.5 goles",
                                "prob": prob_o15,
                                "cuota": cuota_o15,
                                "score": round(score_o15, 1),
                                "fecha": hoy,
                            })

            # ── PUNTO 11: Over 2.5 y Under 2.5 como nuevos mercados ──────
            # Over 2.5 — para partidos claramente ofensivos
            if over25 >= 0.65 and total_prom >= 2.8:
                prob_o25 = _prob_mt(over25 * 100)
                if prom_h2h_mt is not None and prom_h2h_mt < 2.0:
                    pass  # H2H sugiere partidos cerrados
                elif prob_o25 >= 60:
                    cuota_o25, _ = buscar_mejor_cuota(fixture_id, "Over 2.5 goles")
                    if cuota_o25 and MINI_TICKET_CUOTA_MIN <= cuota_o25 <= MINI_TICKET_CUOTA_MAX:
                        clave = (fixture_id, "Over 2.5 goles")
                        if clave not in picks_ya_usados:
                            picks_ya_usados.add(clave)
                            score_o25 = score_por_jugada.get("Over 2.5 goles", score_partido - 0.3)
                            eslabones.append({
                                "fixture_id": fixture_id,
                                "partido": f"{home} vs {away}",
                                "home": home, "away": away,
                                "league": league, "country": country,
                                "hora": hora,
                                "mercado": "Goles totales",
                                "jugada": "Over 2.5 goles",
                                "prob": prob_o25,
                                "cuota": cuota_o25,
                                "score": round(score_o25, 1),
                                "fecha": hoy,
                            })

            # Under 2.5 — para partidos muy defensivos
            if under25 >= 0.70 and total_prom <= 2.0:
                prob_u25 = _prob_mt(under25 * 100)
                if prom_h2h_mt is not None and prom_h2h_mt >= 2.5:
                    pass  # H2H contradice Under 2.5
                elif prob_u25 >= 62:
                    cuota_u25, _ = buscar_mejor_cuota(fixture_id, "Under 2.5 goles")
                    if cuota_u25 and MINI_TICKET_CUOTA_MIN <= cuota_u25 <= MINI_TICKET_CUOTA_MAX:
                        clave = (fixture_id, "Under 2.5 goles")
                        if clave not in picks_ya_usados:
                            picks_ya_usados.add(clave)
                            score_u25 = score_por_jugada.get("Under 2.5 goles", score_partido - 0.2)
                            eslabones.append({
                                "fixture_id": fixture_id,
                                "partido": f"{home} vs {away}",
                                "home": home, "away": away,
                                "league": league, "country": country,
                                "hora": hora,
                                "mercado": "Goles totales",
                                "jugada": "Under 2.5 goles",
                                "prob": prob_u25,
                                "cuota": cuota_u25,
                                "score": round(score_u25, 1),
                                "fecha": hoy,
                            })

            # 2. Doble Oportunidad — buscar cuota real de Pinnacle
            # Calcular fuerza relativa
            gf_h = base_home.get("gf_prom", 0)
            gc_h = base_home.get("gc_prom", 0)
            gf_a = base_away.get("gf_prom", 0)
            gc_a = base_away.get("gc_prom", 0)
            fuerza_h = gf_h - gc_a
            fuerza_a = gf_a - gc_h
            diff = fuerza_h - fuerza_a

            # V14.3: Filtro de probabilidad de empate.
            # Si la prob de empate desde Pinnacle es baja (<18%), 1X/X2
            # tiene poco valor porque la cobertura del empate no suma.
            odds_dc_check = api_get(f"/odds?fixture={fixture_id}", use_cache=True, ttl=600)
            cuotas_1x2_dc = _extraer_cuotas_1x2_pinnacle(odds_dc_check) if odds_dc_check else {}
            prob_empate_real = _prob_empate_desde_cuotas(cuotas_1x2_dc)
            dc_tiene_valor = (prob_empate_real is None or prob_empate_real >= 0.18)

            # Local favorito -> 1X, Visitante favorito -> X2
            if diff >= 0.3:
                jugada_dc = "1X"
                prob_dc = min(85.0, 68.0 + diff * 5)
            elif diff <= -0.3:
                jugada_dc = "X2"
                prob_dc = min(85.0, 68.0 + abs(diff) * 5)
            else:
                jugada_dc = None

            if jugada_dc and dc_tiene_valor:
                cuota_dc, _ = buscar_mejor_cuota(fixture_id, jugada_dc)
                if cuota_dc and MINI_TICKET_CUOTA_MIN <= cuota_dc <= MINI_TICKET_CUOTA_MAX and float(cuota_dc) >= 1.25:
                    clave_dc = (fixture_id, jugada_dc)
                    if clave_dc not in picks_ya_usados:
                        picks_ya_usados.add(clave_dc)
                        prob_dc_cal = _prob_mt(prob_dc)
                        score_dc = score_por_jugada.get(jugada_dc, score_partido)
                        eslabones.append({
                            "fixture_id": fixture_id,
                            "partido": f"{home} vs {away}",
                            "home": home, "away": away,
                            "league": league, "country": country,
                            "hora": hora,
                            "mercado": "Doble oportunidad",
                            "jugada": jugada_dc,
                            "prob": round(prob_dc_cal, 1),
                            "cuota": cuota_dc,
                            "score": round(score_dc, 1),
                            "fecha": hoy,
                        })

            # 3. Sin Tarjeta Roja — SOLO si hay cuota real de Pinnacle
            # No usar cuota estimada en mini-tickets (mismo criterio que handicap)
            liga_sin_stats = any(
                ls.lower() in league.lower()
                for ls in LIGAS_SIN_STATS
            )
            if not liga_sin_stats:
                fase_p = "group"
                if _es_partido_selecciones(league, country):
                    round_p = p.get("round", "")
                    fase_p = _detectar_fase_torneo(league, round_p)

                prob_sin_roja = calcular_prob_sin_roja(home_gen, away_gen, fase_p)
                if prob_sin_roja >= 75:
                    # Buscar cuota REAL de Pinnacle en odds
                    odds_sr = api_get(
                        f"/odds?fixture={fixture_id}",
                        use_cache=True, ttl=600
                    )
                    cuota_sin_roja_real = None
                    if odds_sr:
                        PINNACLE_NAMES = {"Pinnacle", "Pinnacle Sports"}
                        RED_CARD_MARKETS = {"Red Card", "Will There Be a Red Card",
                                           "Red Cards", "Tarjeta Roja"}
                        for casa in odds_sr:
                            for book in casa.get("bookmakers", []):
                                if book.get("name","") not in PINNACLE_NAMES:
                                    continue
                                for bet in book.get("bets", []):
                                    bet_name = bet.get("name","")
                                    if not any(rc.lower() in bet_name.lower()
                                               for rc in RED_CARD_MARKETS):
                                        continue
                                    for value in bet.get("values", []):
                                        if str(value.get("value","")).lower() in ("no","nein","non"):
                                            try:
                                                c_real = float(value.get("odd"))
                                                if c_real > 1.0:
                                                    cuota_sin_roja_real = round(c_real, 3)
                                            except Exception:
                                                pass

                    # Solo agregar si hay cuota real de Pinnacle
                    if cuota_sin_roja_real and MINI_TICKET_CUOTA_MIN <= cuota_sin_roja_real <= MINI_TICKET_CUOTA_MAX:
                        jugada_sr = "Sin Tarjeta Roja"
                        clave_sr = (fixture_id, jugada_sr)
                        if clave_sr not in picks_ya_usados:
                            picks_ya_usados.add(clave_sr)
                            eslabones.append({
                                "fixture_id": fixture_id,
                                "partido": f"{home} vs {away}",
                                "home": home, "away": away,
                                "league": league, "country": country,
                                "hora": hora,
                                "mercado": "Sin Tarjeta Roja",
                                "jugada": jugada_sr,
                                "prob": prob_sin_roja,
                                "cuota": cuota_sin_roja_real,
                                "score": 7.0,
                                "fecha": hoy,
                                # Sin cuota_estimada=True porque es real
                            })

        except Exception as e:
            print(f"WARN mini_ticket partido {p.get('id','?')}: {e}")
            continue

    if not eslabones:
        return []

    # Ordenar eslabones por prob descendente
    eslabones.sort(key=lambda x: x.get("prob", 0), reverse=True)

    # Armar tickets evaluando combinaciones
    tickets_generados = []
    fixtures_usados_en_ticket = set()  # para evitar 3 picks del mismo partido

    for n in [3, 2]:
        if len(tickets_generados) >= MINI_TICKET_MAX_DIA:
            break
        if len(eslabones) < n:
            continue

        for grupo in _comb_mt(eslabones, n):
            if len(tickets_generados) >= MINI_TICKET_MAX_DIA:
                break

            grupo = list(grupo)

            # Verificar max 2 picks del mismo partido
            fids = [e["fixture_id"] for e in grupo]
            from collections import Counter as _Counter
            conteo = _Counter(fids)
            if max(conteo.values()) > 2:
                continue

            # Verificar compatibilidad entre picks del mismo partido
            valido = True
            for i in range(len(grupo)):
                for j in range(i+1, len(grupo)):
                    if grupo[i]["fixture_id"] == grupo[j]["fixture_id"]:
                        if not _son_compatibles(grupo[i]["jugada"], grupo[j]["jugada"]):
                            valido = False
                            break
                if not valido:
                    break
            if not valido:
                continue

            # Calcular cuota y prob conjunta
            # V14.3: aplicar recalibración individual y ajuste de correlación
            cuota_total = 1.0
            prob_conjunta = 1.0
            for e in grupo:
                cuota_total *= e["cuota"]
                prob_e = min(88.0, float(e["prob"]))  # techo 88% por eslabon
                prob_conjunta *= (prob_e / 100.0)
            cuota_total = round(cuota_total, 2)

            # Ajuste de correlación entre mercados del mismo partido
            for i in range(len(grupo)):
                for j in range(i+1, len(grupo)):
                    if grupo[i]["fixture_id"] == grupo[j]["fixture_id"]:
                        prob_conjunta_pct_tmp = prob_conjunta * 100
                        prob_ajustada = _ajustar_prob_correlacion_mismo_partido(
                            grupo[i]["jugada"], grupo[j]["jugada"],
                            prob_conjunta_pct_tmp
                        )
                        prob_conjunta = prob_ajustada / 100.0

            prob_conjunta_pct = round(min(95.0, prob_conjunta * 100), 1)

            # Filtros de calidad
            # P2/P8: Ajuste por correlación entre legs del ticket
        # CQ6/D7: Veto si hay picks del mismo fixture en el ticket
        _picks_ticket_actual = grupo if "grupo" in dir() else []
        if veto_combinada_mismo_fixture(_picks_ticket_actual):
            continue
        if cuota_total < MINI_TICKET_CUOTA_OBJ_MIN:
            continue
        if cuota_total > MINI_TICKET_CUOTA_OBJ_MAX:
            continue
        if prob_conjunta_pct < MINI_TICKET_PROB_MIN:
            continue
        # CQ10: Verificar EV compuesto del ticket completo
        _picks_ev = [{"prob": e.get("prob", 50), "cuota": e.get("cuota", 1.5)} for e in grupo] if "grupo" in dir() else []
        _ev_ticket = calcular_ev_compuesto_ticket(_picks_ev)
        if not _ev_ticket["positivo"] and _ev_ticket.get("ev_pct", 0) < -5:
            continue  # EV muy negativo → descartar ticket

            # Verificar que no repita exactamente el mismo set de picks
            clave_ticket = frozenset(
                (e["fixture_id"], e["jugada"]) for e in grupo
            )
            if any(
                frozenset((e["fixture_id"], e["jugada"]) for e in t["picks"]) == clave_ticket
                for t in tickets_generados
            ):
                continue

            uid = str(_uuid_mt.uuid4())[:5].upper()
            ticket_id = f"MT-{hoy.replace('-','')[2:]}-{uid}"

            ticket = {
                "ticket_id": ticket_id,
                "tipo": "mini_ticket",
                "subtipo": "MT",
                "fecha": hoy,
                "picks": grupo,
                "n_picks": n,
                "cuota_combinada": cuota_total,
                "prob_conjunta": prob_conjunta_pct,
                "estado": "pendiente",
                "timestamp": fecha_hora_peru(),
            }
            tickets_generados.append(ticket)

    # Ordenar por probabilidad descendente
    tickets_generados.sort(key=lambda t: t["prob_conjunta"], reverse=True)

    # V14.3: Diversidad adaptativa según cantidad de eslabones disponibles.
    # Con pocos partidos (días de poca actividad) se relaja a 1 jugada nueva.
    # Con muchos partidos (Mundial) se mantiene en 2 para máxima diversidad.
    min_jugadas_nuevas = 2 if len(eslabones) >= 12 else 1

    tickets_sin_repetir = []
    jugadas_usadas_global = set()

    for ticket in tickets_generados:
        claves_ticket = set(
            (str(e["fixture_id"]), e["jugada"]) for e in ticket["picks"]
        )
        jugadas_nuevas = claves_ticket - jugadas_usadas_global
        if len(jugadas_nuevas) < min_jugadas_nuevas:
            continue
        tickets_sin_repetir.append(ticket)
        jugadas_usadas_global.update(claves_ticket)
        if len(tickets_sin_repetir) >= MINI_TICKET_MAX_DIA:
            break

    return tickets_sin_repetir


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


# Chat IDs que reciben alarmas de combinadas — persistidos en JSON
_CHAT_IDS_ALARMAS = set()


def _cargar_chat_ids_alarmas():
    """Carga los chat_ids desde disco al arrancar."""
    global _CHAT_IDS_ALARMAS
    try:
        data = leer_json(CHAT_IDS_ALARMAS_FILE)
        if isinstance(data, list):
            _CHAT_IDS_ALARMAS = set(str(c) for c in data)
    except Exception:
        pass
    return _CHAT_IDS_ALARMAS


def _guardar_chat_ids_alarmas():
    """Persiste los chat_ids a disco."""
    try:
        guardar_json_lista(CHAT_IDS_ALARMAS_FILE, list(_CHAT_IDS_ALARMAS))
    except Exception as e:
        print(f"WARN guardar chat_ids_alarmas: {e}")


def _registrar_chat_alarma(chat_id):
    """Registra un chat_id para recibir alarmas de combinadas."""
    _CHAT_IDS_ALARMAS.add(str(chat_id))
    _guardar_chat_ids_alarmas()

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
                                elif "sin tarjeta roja" in jugada_comb.lower():
                                    stats_sr = api_get(f"/fixtures/statistics?fixture={fid}", use_cache=False)
                                    rojas_totales = 0
                                    stats_disp = False
                                    if stats_sr:
                                        for td_sr in stats_sr:
                                            stats_disp = True
                                            for item_sr in td_sr.get("statistics", []):
                                                if item_sr.get("type") == "Red Cards":
                                                    val_sr = item_sr.get("value")
                                                    if val_sr is not None:
                                                        try:
                                                            rojas_totales += int(str(val_sr))
                                                        except Exception:
                                                            pass
                                    if not stats_disp:
                                        pick_c["estado"] = "pendiente_manual"
                                        pick_c["resultado_real"] = "Sin stats API — verificar manual"
                                        acierto = None
                                    else:
                                        acierto = rojas_totales == 0
                                        pick_c["resultado_real"] = f"{rojas_totales} rojas"

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


async def enviar_combinada_dia(context: ContextTypes.DEFAULT_TYPE):
    """
    Job automatico 7:30 AM hora Peru (12:30 UTC).
    Genera y envia la combinada garantizada del dia con stake S/25 fijos.
    """
    chat_id = context.job.chat_id
    hoy = fecha_hoy_peru()

    try:
        await context.bot.send_message(
            chat_id=chat_id,
            text="🎯 Generando combinada garantizada del día...",
        )

        # Verificar freno de bank
        bank_data = _leer_bank_acumulado()
        bank_actual = bank_data[-1].get("bank", BANK_INICIAL) if bank_data else BANK_INICIAL
        freno = BANK_INICIAL * BANK_FRENO_PCT
        if bank_actual <= freno:
            await context.bot.send_message(
                chat_id=chat_id,
                text=(
                    f"🛑 *Combinada diaria suspendida*\n"
                    f"Bank actual S/ {bank_actual:.2f} está por debajo del límite de S/ {freno:.2f}.\n"
                    f"Revisa el estado del bank antes de continuar."
                ),
                parse_mode="Markdown"
            )
            return

        # Verificar bank suficiente para el stake
        if bank_actual < STAKE_COMBINADA_DIA * 2:
            await context.bot.send_message(
                chat_id=chat_id,
                text=f"⚠️ Bank insuficiente (S/ {bank_actual:.2f}) para stake de S/ {STAKE_COMBINADA_DIA:.0f}.",
            )
            return

        # Armar combinada del dia con criterios especiales
        comb = _armar_combinada_dia_garantizada()

        if not comb or comb.get("sin_combinada"):
            motivo = comb.get("motivo", "Sin picks suficientes") if comb else "Sin picks disponibles"
            await context.bot.send_message(
                chat_id=chat_id,
                text=(
                    f"⚠️ *Combinada diaria — {hoy}*\n\n"
                    f"No fue posible armar la combinada garantizada hoy.\n"
                    f"Motivo: {motivo}\n\n"
                    f"Usa /analizar para ver los mini-tickets del día."
                ),
                parse_mode="Markdown"
            )
            return

        _guardar_combinada(comb)

        ganancia_pot = round(STAKE_COMBINADA_DIA * (comb["cuota_combinada"] - 1), 2)
        picks = comb["picks"]
        ticket_id = comb.get("ticket_id", "")

        lineas = [
            f"🎯 *COMBINADA GARANTIZADA DEL DÍA — {hoy}*",
            f"🎟 Ticket: `{ticket_id}`",
            "━━━━━━━━━━",
        ]
        for i, p in enumerate(picks, 1):
            cuota_p = _cuota_segura(p)
            lineas.append(
                f"{i}. *{p.get('partido','')}*\n"
                f"   {p.get('league','')} | {p.get('hora','')}\n"
                f"   ✅ {p.get('jugada','')}\n"
                f"   Score: {p.get('score','')} | Prob: {p.get('prob','')}% | Cuota: {cuota_p if cuota_p else 'N/D'}"
            )
        lineas += [
            "━━━━━━━━━━",
            f"📊 Cuota combinada: *{comb['cuota_combinada']}x*",
            f"💰 Stake fijo: *S/ {STAKE_COMBINADA_DIA:.0f}*",
            f"📈 Ganancia potencial: *S/ {ganancia_pot:.2f}*",
            f"📉 Pérdida máxima: *S/ {STAKE_COMBINADA_DIA:.0f}*",
            "",
            "_(Ticket guardado para seguimiento automático)_",
        ]

        await context.bot.send_message(
            chat_id=chat_id,
            text="\n".join(lineas),
            parse_mode="Markdown"
        )

    except Exception as e:
        print(f"ERROR enviar_combinada_dia: {e}")
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text=f"⚠️ Error generando combinada diaria: {e}"
            )
        except Exception:
            pass


async def combinada_dia(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Comando /combinada_dia — genera la combinada garantizada del dia manualmente."""
    _registrar_chat_alarma(update.effective_chat.id)
    await update.message.reply_text("🎯 Generando combinada garantizada del día...")

    # Verificar freno de bank
    bank_data = _leer_bank_acumulado()
    bank_actual = bank_data[-1].get("bank", BANK_INICIAL) if bank_data else BANK_INICIAL
    freno = BANK_INICIAL * BANK_FRENO_PCT
    if bank_actual <= freno:
        await update.message.reply_text(
            f"🛑 *Combinada diaria suspendida*\n"
            f"Bank actual S/ {bank_actual:.2f} está por debajo del límite de S/ {freno:.2f}.",
            parse_mode="Markdown"
        )
        return

    comb = _armar_combinada_dia_garantizada()

    if not comb or comb.get("sin_combinada"):
        motivo = comb.get("motivo", "Sin picks suficientes") if comb else "Sin picks disponibles"
        await update.message.reply_text(
            f"⚠️ No fue posible armar la combinada garantizada hoy.\n"
            f"Motivo: {motivo}\n\n"
            f"Usa /analizar para ver los mini-tickets del día."
        )
        return

    _guardar_combinada(comb)

    ganancia_pot = round(STAKE_COMBINADA_DIA * (comb["cuota_combinada"] - 1), 2)
    picks = comb["picks"]
    ticket_id = comb.get("ticket_id", "")
    hoy = fecha_hoy_peru()

    lineas = [
        f"🎯 *COMBINADA GARANTIZADA DEL DÍA — {hoy}*",
        f"🎟 Ticket: `{ticket_id}`",
        "━━━━━━━━━━",
    ]
    for i, p in enumerate(picks, 1):
        cuota_p = _cuota_segura(p)
        lineas.append(
            f"{i}. *{p.get('partido','')}*\n"
            f"   {p.get('league','')} | {p.get('hora','')}\n"
            f"   ✅ {p.get('jugada','')}\n"
            f"   Score: {p.get('score','')} | Prob: {p.get('prob','')}% | Cuota: {cuota_p if cuota_p else 'N/D'}"
        )
    lineas += [
        "━━━━━━━━━━",
        f"📊 Cuota combinada: *{comb['cuota_combinada']}x*",
        f"💰 Stake fijo: *S/ {STAKE_COMBINADA_DIA:.0f}*",
        f"📈 Ganancia potencial: *S/ {ganancia_pot:.2f}*",
        f"📉 Pérdida máxima: *S/ {STAKE_COMBINADA_DIA:.0f}*",
        "",
        "_(Ticket guardado para seguimiento automático)_",
    ]

    await update.message.reply_text(
        "\n".join(lineas),
        parse_mode="Markdown"
    )


async def handicap(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /handicap — Analiza todos los partidos del dia y sugiere handicap asiatico.
    MODO OBSERVACION: no afecta el bank. Solo acumula base de datos.
    Solo recomienda picks con cuota real de Pinnacle >= HANDICAP_CUOTA_MIN.
    """
    _registrar_chat_alarma(update.effective_chat.id)
    hoy = fecha_hoy_peru()
    ahora_ts = int(fecha_peru_obj().timestamp())

    # Estadisticas acumuladas
    data_ha = leer_json(HANDICAP_FILE)
    total_ha = len(data_ha)
    cerrados_ha = [r for r in data_ha if r.get("estado") in ("acierto","fallo","push")]
    n_cerrados = len(cerrados_ha)
    aciertos_ha = sum(1 for r in cerrados_ha if r.get("estado") == "acierto")
    fallos_ha = sum(1 for r in cerrados_ha if r.get("estado") == "fallo")
    validos_ha = aciertos_ha + fallos_ha
    ef_ha = round(aciertos_ha / validos_ha * 100, 1) if validos_ha else 0

    if n_cerrados < HANDICAP_PICKS_MIN_CONFIANZA:
        nivel = f"⚠️ Modo observación — faltan {HANDICAP_PICKS_MIN_CONFIANZA - n_cerrados} picks para confiar"
    elif n_cerrados < 60:
        nivel = "🟡 Datos preliminares — usar con cautela"
    else:
        nivel = "✅ Base de datos suficiente"

    await update.message.reply_text(
        f"🔬 *Handicap Asiático — Modo Observación*\n"
        f"📊 Base: {n_cerrados} cerrados / {total_ha} total | Efectividad: {ef_ha}%\n"
        f"{nivel}\n\n"
        f"Analizando partidos del día... esto puede tomar 1-2 minutos.",
        parse_mode="Markdown"
    )

    # Construir lista de ligas
    ligas = {}
    ligas.update(EUROPA_LEAGUES)
    ligas.update(SUDAMERICA_LEAGUES)
    ligas.update(OTRAS_LEAGUES)
    ligas.update(SELECCIONES_LEAGUES)

    partidos = obtener_fixtures_por_fecha(ligas, hoy)
    partidos_futuros = [
        p for p in partidos
        if p.get("timestamp", 0) - ahora_ts > 1800
    ]

    if not partidos_futuros:
        await update.message.reply_text("❌ No hay partidos disponibles con más de 30 minutos de anticipación.")
        return

    # Prefetch de odds en paralelo
    try:
        import aiohttp as _aiohttp_ha
        fixture_ids_ha = [str(p["id"]) for p in partidos_futuros]

        async def _prefetch_ha(fids):
            async with _aiohttp_ha.ClientSession() as sess:
                tasks = [
                    api_get_async(sess, f"/odds?fixture={fid}", use_cache=True, ttl=600)
                    for fid in fids
                ]
                await asyncio.gather(*tasks, return_exceptions=True)

        for i in range(0, len(fixture_ids_ha), 10):
            await _prefetch_ha(fixture_ids_ha[i:i+10])
            await asyncio.sleep(0.3)
    except Exception:
        pass

    picks_ha = []
    guardados_hoy = set(
        (str(r.get("fixture_id","")), r.get("equipo",""), str(r.get("linea","")))
        for r in data_ha if r.get("fecha","")[:10] == hoy
    )

    for p in partidos_futuros:
        if len(picks_ha) >= MAX_HANDICAP_DIA:
            break
        try:
            fixture_id = str(p["id"])
            home = p["home"]
            away = p["away"]
            league = p["league"]
            country = p.get("country","")
            hora = p.get("hour","")

            odds = api_get(f"/odds?fixture={fixture_id}", use_cache=True, ttl=600)
            if not odds:
                continue

            es_seleccion = _es_partido_selecciones(league, country)

            if es_seleccion:
                rec_ha = calcular_handicap_recomendado_seleccion(home, away, odds)
            else:
                home_general = calcular_forma(p.get("home_id") or
                    api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)[0]["teams"]["home"]["id"]
                    if not p.get("home_id") else p["home_id"])
                away_general = calcular_forma(p.get("away_id") or
                    api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)[0]["teams"]["away"]["id"]
                    if not p.get("away_id") else p["away_id"])

                if not home_general or not away_general:
                    continue

                home_home = calcular_forma(
                    api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)[0]["teams"]["home"]["id"],
                    "home"
                )
                away_away = calcular_forma(
                    api_get(f"/fixtures?id={fixture_id}", use_cache=True, ttl=3600)[0]["teams"]["away"]["id"],
                    "away"
                )
                rec_ha = calcular_handicap_recomendado_club(
                    home_general, away_general, home_home, away_away, odds
                )

            if not rec_ha:
                continue

            equipo = rec_ha["equipo"]
            linea = rec_ha["linea"]
            cuota = rec_ha["cuota"]

            # Verificar duplicado del dia
            clave = (fixture_id, equipo, str(linea))
            if clave in guardados_hoy:
                continue

            equipo_nombre = home if equipo == "home" else away
            jugada = f"{equipo_nombre} {linea:+.2f}"

            registro = {
                "fixture_id": fixture_id,
                "partido": f"{home} vs {away}",
                "home": home,
                "away": away,
                "league": league,
                "country": country,
                "hora": hora,
                "fecha": hoy,
                "equipo": equipo,
                "linea": linea,
                "jugada": jugada,
                "cuota": cuota,
                "bookmaker": rec_ha.get("bookmaker","Pinnacle"),
                "prob_estimada": rec_ha.get("prob_estimada", 0),
                "tipo_equipo": "seleccion" if es_seleccion else "club",
                "modo": "observacion",
                "estado": "pendiente",
                "resultado": None,
                "resultado_real": None,
                "gh": None,
                "ga": None,
                "retorno": None,
                "timestamp": fecha_hora_peru(),
            }

            guardado = guardar_handicap(registro)
            if guardado:
                picks_ha.append(registro)
                guardados_hoy.add(clave)

        except Exception as e:
            print(f"WARN handicap partido {p.get('id','?')}: {e}")
            continue

    if not picks_ha:
        await update.message.reply_text(
            "❌ No encontré picks de handicap para hoy.\n"
            "Pinnacle no tiene cuotas de Asian Handicap disponibles para los partidos de hoy, "
            "o todos los partidos son muy parejos para recomendar."
        )
        return

    texto = f"🔬 *Handicap Asiático del día — {hoy}*\n"
    texto += f"_{len(picks_ha)} picks encontrados con cuota real de Pinnacle_\n"
    texto += "⚠️ *MODO OBSERVACIÓN — No apostar hasta tener 30+ picks cerrados*\n"
    texto += "━━━━━━━━━━\n\n"

    for i, r in enumerate(picks_ha, 1):
        tipo = "🌍 SELECCIÓN" if r.get("tipo_equipo") == "seleccion" else "⚽ Club"
        texto += (
            f"{i}. *{r['partido']}*\n"
            f"   {r['league']} | {r['hora']} | {tipo}\n"
            f"   ✅ *{r['jugada']}*\n"
            f"   Cuota: *{r['cuota']}x* (Pinnacle) | Prob estimada: {r['prob_estimada']}%\n\n"
        )

    texto += (
        f"📊 *Base acumulada:* {n_cerrados} cerrados | {ef_ha}% efectividad\n"
        f"_Picks guardados en seguimiento. Usa /handicap_stats para ver estadísticas._"
    )

    await _enviar_mensaje_paginado(update, texto)


async def handicap_stats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /handicap_stats — Estadísticas acumuladas del handicap asiático.
    """
    cerrar_handicaps_pendientes()
    data = leer_json(HANDICAP_FILE)

    if not data:
        await update.message.reply_text(
            "📊 Aún no hay picks de handicap registrados.\nUsa /handicap para empezar."
        )
        return

    cerrados = [r for r in data if r.get("estado") in ("acierto","fallo","push")]
    pendientes = [r for r in data if r.get("estado") == "pendiente"]
    aciertos = sum(1 for r in cerrados if r.get("estado") == "acierto")
    fallos = sum(1 for r in cerrados if r.get("estado") == "fallo")
    push = sum(1 for r in cerrados if r.get("estado") == "push")
    validos = aciertos + fallos
    ef = round(aciertos / validos * 100, 1) if validos else 0
    roi_sim = sum(r.get("retorno", 0) for r in cerrados)

    if validos < HANDICAP_PICKS_MIN_CONFIANZA:
        nivel = f"⚠️ Insuficiente — faltan {HANDICAP_PICKS_MIN_CONFIANZA - validos} picks válidos"
    elif validos < 60:
        nivel = "🟡 Preliminar — usar con cautela"
    else:
        nivel = "✅ Confiable"

    # Por linea
    por_linea = {}
    for r in cerrados:
        ln = str(r.get("linea","?"))
        por_linea.setdefault(ln, {"ok":0,"fallo":0,"push":0})
        est = r.get("estado","")
        if est == "acierto": por_linea[ln]["ok"] += 1
        elif est == "fallo": por_linea[ln]["fallo"] += 1
        elif est == "push": por_linea[ln]["push"] += 1

    # Por tipo
    clubs = [r for r in cerrados if r.get("tipo_equipo") != "seleccion"]
    sels = [r for r in cerrados if r.get("tipo_equipo") == "seleccion"]
    ef_club = round(sum(1 for r in clubs if r.get("estado")=="acierto") / max(len([r for r in clubs if r.get("estado") in ("acierto","fallo")]),1) * 100, 1)
    ef_sel = round(sum(1 for r in sels if r.get("estado")=="acierto") / max(len([r for r in sels if r.get("estado") in ("acierto","fallo")]),1) * 100, 1)

    texto = (
        f"🔬 *Handicap Asiático — Estadísticas*\n"
        f"━━━━━━━━━━\n"
        f"📊 Total picks: {len(data)}\n"
        f"✅ Cerrados: {len(cerrados)} | ⏳ Pendientes: {len(pendientes)}\n"
        f"✅ Aciertos: {aciertos} | ❌ Fallos: {fallos} | 🔄 Push: {push}\n"
        f"🎯 Efectividad: *{ef}%*\n"
        f"💰 ROI simulado (1u/pick): *{roi_sim:+.2f}u*\n"
        f"📈 Nivel: {nivel}\n\n"
        f"*Por tipo de equipo:*\n"
        f"⚽ Clubes: {ef_club}% ({len([r for r in clubs if r.get('estado') in ('acierto','fallo')])} válidos)\n"
        f"🌍 Selecciones: {ef_sel}% ({len([r for r in sels if r.get('estado') in ('acierto','fallo')])} válidos)\n\n"
        f"*Por línea de handicap:*\n"
    )
    for ln, v in sorted(por_linea.items()):
        tot = v["ok"] + v["fallo"]
        ef_ln = round(v["ok"] / tot * 100, 1) if tot else 0
        texto += f"  Línea {ln}: {v['ok']}✅ {v['fallo']}❌ {v['push']}🔄 — {ef_ln}%\n"

    await _enviar_mensaje_paginado(update, texto)


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
                await asyncio.sleep(1.0)  # 1s entre lotes para evitar ráfagas
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
    ligas_todas.update(SELECCIONES_LEAGUES)

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
                score_rec = float(top.get("score", 0) or 0)
                # V14.2: filtrar por SCORE como criterio principal (no prob)
                if score_rec < 7.5:
                    continue

                # Limit: max MAX_PICKS_DIA picks por dia
                if len(picks_encontrados) >= MAX_PICKS_DIA:
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
                "riesgo": float(mejor.get("riesgo", 5) or 5),
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
ESCALERA_CUOTA_MIN = 1.50   # Consistente con CUOTA_MINIMA_PICK del sistema

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

# Ranking FIFA oficial — actualizado a abril 2026 (ultimo antes del Mundial)
# Proxima actualizacion oficial: 11 junio 2026 (inicio del Mundial)
RANKING_FIFA = {
    # Top 20 (fuente: FIFA oficial abril 2026)
    "France": 1, "Spain": 2, "Argentina": 3, "England": 4,
    "Portugal": 5, "Brazil": 6, "Netherlands": 7, "Morocco": 8,
    "Belgium": 9, "Germany": 10, "Croatia": 11, "Italy": 12,
    "Colombia": 13, "Senegal": 14, "Mexico": 15, "United States": 16,
    "USA": 16, "Uruguay": 17, "Japan": 18, "Switzerland": 19,
    "Denmark": 20,
    # 21-50
    "Ecuador": 21, "Austria": 22, "South Korea": 23, "Hungary": 24,
    "Turkey": 25, "Türkiye": 25, "Australia": 26, "Canada": 27,
    "Ukraine": 28, "Norway": 29, "Panama": 30, "Poland": 31,
    "Wales": 32, "Chile": 32, "Algeria": 34, "Egypt": 35,
    "Scotland": 36, "Serbia": 37, "Nigeria": 38, "Paraguay": 39,
    "Peru": 40, "Tunisia": 41, "Ivory Coast": 42, "Côte d'Ivoire": 42,
    "Sweden": 43, "Czech Republic": 44, "Czechia": 44, "Slovakia": 45,
    "Greece": 46, "Romania": 47, "Venezuela": 48, "Costa Rica": 49,
    "Uzbekistan": 50,
    # Equipos clasificados al Mundial 2026 — V14.3 completado
    "Qatar": 53, "Saudi Arabia": 56, "South Africa": 61,
    "Jordan": 64, "Cabo Verde": 67, "Cape Verde": 67,
    "Ghana": 72, "Curaçao": 82, "Curacao": 82, "Haiti": 84,
    "New Zealand": 87, "Honduras": 65, "Bolivia": 85,
    "Iraq": 64, "Indonesia": 130,
    # V14.3: equipos adicionales del Mundial 2026
    "Guatemala": 110, "El Salvador": 96,
    "Congo DR": 55, "DR Congo": 55, "Tanzania": 121,
    "Bahrain": 86, "China": 92, "Chinese Taipei": 130,
    "Sudan": 130, "South Sudan": 130,
    "Thailand": 113, "Philippines": 134, "Myanmar": 160,
    "Cambodia": 175, "Vietnam": 116,
    "Kosovo": 100, "Luxembourg": 95, "Gibraltar": 198,
    "Faroe Islands": 115, "Armenia": 104, "Georgia": 75,
    "Slovenia": 57, "Iceland": 68, "Albania": 69, "Finland": 52,
    "North Macedonia": 73, "Bosnia": 63, "Bosnia and Herzegovina": 63,
    "Bulgaria": 78, "Israel": 76, "Montenegro": 94,
    "Cameroon": 47, "Mali": 56, "Zambia": 95, "Angola": 99,
    "Benin": 96, "Guinea": 79, "Comoros": 102, "Namibia": 107,
    "Libya": 111, "Ethiopia": 117, "Mozambique": 120,
    "Trinidad and Tobago": 88, "Jamaica": 55, "Cuba": 116,
    "Guyana": 122, "Suriname": 105, "Belize": 163,
    "Oman": 80, "Kuwait": 130, "Lebanon": 101, "Kyrgyzstan": 109,
    "Tajikistan": 108, "Myanmar": 160, "Mongolia": 185,
    "Northern Ireland": 70, "Republic of Ireland": 51, "Ireland": 51,
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
        "mercados_preferidos": ["Over 1.5 goles", "Doble Oportunidad", "Under 3.5 goles"],
        "mercados_evitar": ["Ambos marcan - Si", "Corners Over 9.5"],
        "ajuste_score": -0.5,
        "nota": "Amistosos: rotacion de jugadores, menor motivacion defensiva. Evitar corners.",
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
    # N4: Estadio Azteca (Mexico City) — altitud 2240m genera +0.15 goles
    # en minutos 75-90 por menor presión de oxígeno que afecta al equipo
    # visitante más que al local en fases tardías del partido.
    _azteca_bonus = 0.15 if sede == "Mexico City" and altitud >= 2000 else 0.0

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

    # 9. V15: Ajuste calor Mundial 2026 (X5-X7, X14-X15)
    _es_mundial = any(x in league.lower() for x in ["world cup", "mundial", "fifa"])
    if _es_mundial and sede:
        # Detectar jornada para pasar el parámetro correcto
        _jornada_num = 1
        if _es_j2: _jornada_num = 2
        elif _es_j3: _jornada_num = 3
        elif fase in ("round_of_16",): _jornada_num = 4
        elif fase in ("quarter",): _jornada_num = 5
        elif fase in ("semi", "final"): _jornada_num = 6
        _calor = ajuste_xg_calor_mundial(sede, home, away, jornada_torneo=_jornada_num)
        score_base += _calor["ajuste_score"]

    # N4: Bonus altitud Azteca en goles esperados
    if _azteca_bonus > 0:
        score_base += 0.1

    # NM5/W6: Ajuste Under 3.5 en semis y finales del Mundial
    if _es_mundial and fase in ("semi", "final"):
        _prob_u35_fase = prob_under35_por_fase(fase)
        # Si el modelo también lo indica → el pick tiene doble confirmación
        score_base += 0.2  # bonus por convergencia histórico + modelo

    # W7/W11: Fatiga y rotaciones
    if _es_mundial:
        _fatiga = ajuste_fatiga_mundial(
            dias_descanso_home=desc_home if desc_home < 99 else 5,
            dias_descanso_away=desc_away if desc_away < 99 else 5,
            jornada=_jornada_num if "_jornada_num" in dir() else 1,
        )
        score_base += _fatiga["ajuste_score"]
        # W11: Rotaciones J3
        if _es_j3:
            _rots = detectar_rotaciones_j3(
                bajas_confirmadas=bajas_home + bajas_away,
                es_j3=True,
                ya_clasificado=False,
            )
            score_base += _rots["ajuste_score"]

    # W14: xGD acumulado en el torneo
    _goles_torneo_home = [gf_home] * min(3, len(home_fixtures or []))
    _goles_contra_home = [gc_home] * min(3, len(home_fixtures or []))
    _xgd_torneo_home = xgd_acumulado_torneo(_goles_torneo_home, _goles_contra_home)
    # Bonus score si el equipo domina xGD en el torneo
    if _xgd_torneo_home >= 3 and _es_mundial:
        score_base += 0.15
    elif _xgd_torneo_home <= -3 and _es_mundial:
        score_base -= 0.15

    # W9: DC underdog cuando diff Elo aprox < 250 en grupos Mundial
    # Upsets ocurren en 35% de partidos con diff moderada — señal para DC del underdog
    _diff_elo_aprox = abs(diff_ranking) * 3
    if _es_mundial and fase == "group" and 50 < _diff_elo_aprox < 250:
        # Diferencia moderada: el mercado sobrevalora al favorito leve
        # Este flag se usa para sugerir DC en lugar de 1X2 del favorito
        pass  # W9 actua a nivel de sugerencia de mercado en el mensaje final

    # W1/W2: Ajuste jornada Mundial (J1 Under / J2 Over / J3 rotaciones)
    if _es_mundial and (_es_j1 or _es_j2 or _es_j3):
        score_base += _ajuste_jornada_goles

    # W4: Factor motivacion J3
    if _es_mundial and _es_j3:
        _mot_j3 = evaluar_motivacion_j3(
            ya_clasificado_home=False,   # detectar desde API standings si disponible
            ya_clasificado_away=False,
            eliminado_home=False,
            eliminado_away=False,
        )
        score_base += _mot_j3["ajuste_score"]

    # P5: Upsets grupo Mundial 35% → DC underdog
    if _es_mundial and fase == "group":
        _upset_dc = evaluar_upset_dc_underdog(
            cuota_underdog=None,  # se actualizará con cuota real en enriquecer_con_odds
            diff_elo_aprox=abs(diff_ranking) * 3,
            fase=fase,
            es_mundial=True,
        )
        # El resultado se guardará en el analisis para usarlo en el mensaje

    # P6: Señales live calculables prematch
    _señales_live = calcular_señales_live_prematch(
        prob_home=60.0, prob_draw=22.0, prob_away=18.0,  # valores aproximados
        cuota_home=1.0 / max(0.01, 0.60), cuota_away=1.0 / max(0.01, 0.18),
    )

    # W12: Draw táctico J3 — a ambos les sirve el empate
    if _es_mundial and _es_j3:
        _draw_tact = detectar_draw_tactico_j3(
            ya_clasificado_home=False,
            ya_clasificado_away=False,
            resultado_sirve_empate_home=(forma_home.count("D") >= 1 if forma_home else False),
            resultado_sirve_empate_away=(forma_away.count("D") >= 1 if forma_away else False),
        )
        if _draw_tact["draw_tactico"]:
            score_base -= 0.3  # partido conservador reduce certeza del pick

    # W10: Rebote emocional J2 tras derrota en J1
    if _es_mundial and _es_j2:
        _home_perdio_j1 = forma_home and forma_home[-1:] == "L"
        _away_perdio_j1 = forma_away and forma_away[-1:] == "L"
        _rebote_j2 = evaluar_rebote_emocional_j2(
            perdio_j1_home=bool(_home_perdio_j1),
            perdio_j1_away=bool(_away_perdio_j1),
        )
        score_base += _rebote_j2["ajuste_score"]

    # W13: Under 1.0 HT en J1
    if _es_mundial and _es_j1:
        _ht_eval = evaluar_under10_primer_tiempo_j1(
            es_j1=True,
            estilo_home=estilo_home,
            estilo_away=estilo_away,
        )
        # El pick HT se agrega al contexto del analisis, no al score principal

    # 10. V15: xPTS gap y eficiencia ofensiva — aplicar si hay datos
    score_base = round(score_base, 2)

    score_final = round(min(10.0, max(5.0, score_base)), 1)

    # V17: Motivación diferencial cuantificada
    _mot_diff = calcular_motivacion_diferencial(
        int(home_puntos or 0), int(away_puntos or 0),
        int(ctx.get("home_partidos_jugados") or 20),
        str(ctx.get("home_descripcion") or ""),
        str(ctx.get("away_descripcion") or ""),
        int(ctx.get("home_posicion") or 10),
        int(ctx.get("away_posicion") or 10),
    )
    if _mot_diff["ajuste"] > 0:
        score_base += _mot_diff["ajuste"] * 0.5

    # O12/P12: Mismatch Mundial Over 3.5
    if _es_mundial and fase == "group":
        _btts_underdog_rate = 30  # estimado; el underdog marca ~30% de veces
        _o12 = evaluar_mismatch_over35_mundial(
            diff_ranking_fifa=abs(diff_ranking),
            btts_rate_underdog=_btts_underdog_rate,
            xg_combinado=gf_home + gf_away,
            es_mundial=True,
        )
        if _o12["recomendar"]:
            score_base += 0.2  # bonus al análisis general del partido

    # Z15: AH preferible sobre DC cuando hay diff xG clara en Mundial
    if _es_mundial:
        _xg_diff_sel = abs(gf_home - gf_away)  # proxy xG diff
        _z15 = preferir_ah_sobre_dc_mundial(
            xg_diff=_xg_diff_sel,
            es_mundial=True,
            cuota_dc=1.45,   # estimado; se actualiza con real
            cuota_ah=1.85,
        )
        # Se guarda el resultado para incluirlo en el mensaje

    # ── PROBABILIDADES HISTORICAS POR FASE ───────────────────────────
    # Under 2.5: grupos 59%, octavos 62%, cuartos 65%, semis 70%, final 68%
    # W1: Ajustes J1/J2/J3 por histórico goles mundiales
    # J1=2.38 goles/pto (Under valor), J2=2.94 (Over valor), J3=2.31 (rotaciones, Under)
    # Formato 48: J3 Over por equipos que luchan por goal difference (W2)
    _es_j1 = round_name and ("matchday 1" in round_name.lower() or "jornada 1" in round_name.lower() or "group stage - 1" in round_name.lower())
    _es_j2 = round_name and ("matchday 2" in round_name.lower() or "jornada 2" in round_name.lower() or "group stage - 2" in round_name.lower())
    _es_j3 = round_name and ("matchday 3" in round_name.lower() or "jornada 3" in round_name.lower() or "group stage - 3" in round_name.lower())
    _ajuste_jornada_goles = 0.0
    if _es_j1:
        _ajuste_jornada_goles = -0.10  # J1: 2.38 goles — Under tiene valor histórico
    elif _es_j2:
        _ajuste_jornada_goles = +0.15  # J2: 2.94 goles — Over tiene valor histórico
    elif _es_j3:
        _ajuste_jornada_goles = -0.08  # J3: 2.31 goles — rotaciones reducen goles

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
        # V14.3: Descarte directo si H2H promedio supera la línea
        if goles_h2h_prom >= 2.5:
            pass  # partido históricamente goleador — no recomendar Under 2.5
        else:
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

    # Under 3.5 goles — V14.3: usa Poisson+Dixon-Coles en lugar de Under2.5+14
    if "Under 3.5 goles" in mercados_pref:
        # Descarte directo si H2H promedio supera la línea
        if goles_h2h_prom >= 3.5:
            pass  # partido históricamente muy goleador — no recomendar Under 3.5
        else:
            # Usar Poisson con datos reales en lugar de fórmula arbitraria
            prob_u35_poisson = prob_under35_poisson(
                gf_home, gc_home, gf_away, gc_away, league
            )
            prob_u35 = prob_u35_poisson if prob_u35_poisson else min(88, prob_under25_base + 14)
            # Ajuste por fase — en grupos hay más Under 3.5 que en eliminatorias
            if fase == "friendly":
                prob_u35 = max(40, prob_u35 - 8)  # amistosos más abiertos
            prob_u35 = min(88, prob_u35)
            sugerencias.append({
                "mercado": "Goles",
                "jugada": "Under 3.5 goles",
                "prob": round(prob_u35, 1),
                "score": score_final,
                "riesgo": 1.2,
                "cuota_minima": cuota_minima(prob_u35/100, 1.2),
                "cuota": cuota_minima(prob_u35/100, 1.2),
                "confianza": etiqueta_confianza(score_final),
                "motivo": f"Partidos cerrados — {estilo_home} vs {estilo_away} | Poisson: {prob_u35:.0f}%",
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

        # V14.3: Filtro de prob de empate desde Pinnacle
        # Si la prob de empate es baja (<18%) el pick DC tiene poco valor real
        try:
            odds_do = api_get(f"/odds?fixture={fixture_id}", use_cache=True, ttl=600)
            cuotas_do = _extraer_cuotas_1x2_pinnacle(odds_do) if odds_do else {}
            prob_empate_do = _prob_empate_desde_cuotas(cuotas_do)
            dc_sel_tiene_valor = (prob_empate_do is None or prob_empate_do >= 0.18)
        except Exception:
            dc_sel_tiene_valor = True

        if dc_sel_tiene_valor:
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

    # Corners (V14.3: usar promedio real de corners por partido via analizar_estilo_corners)
    # Solo recomendar si la suma de corners promedio home+away supera la línea en ≥1.5
    # No recomendar en amistosos ni ligas sudamericanas (promedio corners bajo)
    if any("Corner" in m for m in mercados_pref):
        ligas_sin_corners = ["friendly", "amistoso", "sudamericana", "libertadores",
                             "primera division", "liga colombiana", "liga mx",
                             "serie a brasil", "urugua", "argentin", "chile",
                             "u19", "u20", "u21", "u-19", "u-20", "u-21"]
        liga_baja_corners = any(k in (league or "").lower() for k in ligas_sin_corners)

        if not liga_baja_corners:
            corner_jugada = next((m for m in mercados_pref if "Corner" in m), "Corners Over 9.5")
            # Extraer línea de la jugada (ej: "Corners Over 9.5" → 9.5)
            import re as _re_corn
            m_linea = _re_corn.search(r"(\d+\.?\d*)", corner_jugada)
            linea_corner = float(m_linea.group(1)) if m_linea else 9.5

            # Obtener promedio real de corners de cada equipo
            try:
                estilo_h = analizar_estilo_corners(home_id, last=8) if home_id else None
                estilo_a = analizar_estilo_corners(away_id, last=8) if away_id else None
                corners_h = estilo_h.get("corners_prom", 0) if estilo_h else 0
                corners_a = estilo_a.get("corners_prom", 0) if estilo_a else 0
                corners_esperados = corners_h + corners_a
            except Exception:
                corners_esperados = 0

            # Solo recomendar si corners esperados superan la línea en ≥1.5
            if corners_esperados >= (linea_corner + 1.5):
                prob_corner = min(78, 55 + (corners_esperados - linea_corner) * 8)
                if estilo_h and estilo_h.get("estilo") == "costados":
                    prob_corner = min(80, prob_corner + 5)
                if estilo_a and estilo_a.get("estilo") == "costados":
                    prob_corner = min(80, prob_corner + 5)
                sugerencias.append({
                    "mercado": "Corners",
                    "jugada": corner_jugada,
                    "prob": round(prob_corner, 1),
                    "score": round(score_final - 0.2, 1),
                    "riesgo": 1.8,
                    "cuota_minima": cuota_minima(prob_corner/100, 1.8),
                    "cuota": cuota_minima(prob_corner/100, 1.8),
                    "confianza": etiqueta_confianza(score_final - 0.2),
                    "motivo": f"Corners esperados: {corners_esperados:.1f} (línea {linea_corner}) | {estilo_h.get('estilo','?') if estilo_h else '?'} vs {estilo_a.get('estilo','?') if estilo_a else '?'}",
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

    # V14.3: Aplicar penalización por tipo de competición (Sub-19/20/21)
    pen_comp_sel = _penalizacion_competicion(league)
    if pen_comp_sel != 0:
        for s in sugerencias:
            s["score"] = round(max(0, s["score"] + pen_comp_sel), 1)

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
app.add_handler(CommandHandler("handicap", handicap))
app.add_handler(CommandHandler("handicap_stats", handicap_stats))
app.add_handler(CommandHandler("combinada_dia", combinada_dia))
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


async def cmd_calibrar(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """V15: Reporte de calibracion de probabilidades y CLV por mercado."""
    await update.message.reply_text("Analizando calibracion del modelo...")
    datos = leer_json(APRENDIZAJE_FILE)
    if not datos:
        await update.message.reply_text("No hay datos en aprendizaje.json")
        return
    cal = calibrar_por_mercado(datos)
    clv = analizar_clv_historico(datos)
    lineas = ["[CAL V15] picks=" + str(cal["total_picks_analizados"])]
    if cal["sesgos_criticos"]:
        lineas.append("Sesgos criticos detectados:")
        for clave, v in list(cal["sesgos_criticos"].items())[:8]:
            mercado_txt = clave.split("|")[0]
            rango_txt = clave.split("|")[1] if "|" in clave else ""
            sesgo = v["sesgo_pct"]
            tipo = "sobreconfianza" if v["sobreconfianza"] else "infraconfianza"
            lineas.append(f"  {mercado_txt} {rango_txt}: {tipo} {sesgo:+.0f}% ({v['n_picks']} picks)")
    else:
        lineas.append("Sin sesgos criticos detectados")
    if clv:
        lineas.append("CLV por mercado:")
        for clave, v in list(clv.items())[:8]:
            mercado_txt = clave.split("|")[0]
            jugada_txt = clave.split("|")[1] if "|" in clave else ""
            edge = "OK" if v["tiene_edge"] else "NO"
            lineas.append(f"  {edge} {mercado_txt} {jugada_txt}: CLV {v['clv_promedio']:+.1f}pp ({v['pct_positivo']:.0f}% pos, n={v['n_picks']})")
    await update.message.reply_text("\n".join(lineas))

app.add_handler(CommandHandler("calibrar", cmd_calibrar))

print("🤖 HarryNine V15 ejecutándose...")
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

# Cargar chat_ids de alarmas persistidos (sobreviven reinicios)
_cargar_chat_ids_alarmas()

# Job GLOBAL de actualizacion de estados cada 20 minutos
# Independiente de alertas — siempre activo.
app.job_queue.run_repeating(
    _job_actualizar_estados,
    interval=1200,   # cada 20 minutos
    first=30,
    name="auto_update_estados_global",
)

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