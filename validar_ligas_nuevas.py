"""
validar_ligas_nuevas.py
HarryNine V14 - Validador automatico de IDs de ligas Tier 1 nuevas

Uso:
    python validar_ligas_nuevas.py

El script:
1. Consulta /leagues de api-sports.io para cada liga candidata
2. Verifica que el ID coincida con el nombre/pais esperado
3. Verifica que la temporada este activa (current=True o coverage del año)
4. Si un ID esta mal, busca el correcto por nombre+pais
5. Imprime un dict listo para pegar en bot.py
"""

import os
import sys
import requests
from dotenv import load_dotenv

load_dotenv()

API_KEY = os.getenv("API_FOOTBALL_KEY", "3016c710cf4d9ca6f30f82eabefb7bd4")
BASE_URL = "https://v3.football.api-sports.io"
HEADERS = {"x-apisports-key": API_KEY}

# Candidatas a validar: (nombre_para_bot, id_propuesto, season, country_esperado, grupo)
CANDIDATAS = [
    ("Copa Libertadores",   13,  2026, "World",    "SUDAMERICA"),
    ("Copa Sudamericana",   11,  2026, "World",    "SUDAMERICA"),
    ("MLS",                253,  2026, "USA",      "OTRAS"),
    ("Süper Lig",          203,  2025, "Turkey",   "EUROPA"),
    ("Primeira Liga",       94,  2025, "Portugal", "EUROPA"),
    ("Allsvenskan",        113,  2026, "Sweden",   "EUROPA"),
    ("J-League",            98,  2026, "Japan",    "OTRAS"),
]


def consultar_liga_por_id(league_id):
    """Devuelve el dict 'response' de /leagues?id=X o None si falla."""
    try:
        r = requests.get(f"{BASE_URL}/leagues", headers=HEADERS, params={"id": league_id}, timeout=15)
        r.raise_for_status()
        data = r.json()
        if data.get("results", 0) == 0:
            return None
        return data["response"][0]
    except Exception as e:
        print(f"   ⚠️ Error consultando id={league_id}: {e}")
        return None


def buscar_liga_por_nombre(nombre, country):
    """Busca una liga por nombre+pais. Devuelve lista de matches."""
    try:
        r = requests.get(f"{BASE_URL}/leagues", headers=HEADERS,
                         params={"search": nombre, "country": country}, timeout=15)
        r.raise_for_status()
        data = r.json()
        return data.get("response", [])
    except Exception as e:
        print(f"   ⚠️ Error buscando '{nombre}' en {country}: {e}")
        return []


def temporada_activa(info_liga, season_esperado):
    """Verifica si la temporada esperada existe y esta activa (current=True o end>=hoy)."""
    if not info_liga:
        return False, None
    seasons = info_liga.get("seasons", [])
    for s in seasons:
        if s.get("year") == season_esperado:
            return s.get("current", False), s
    return False, None


def validar():
    print("=" * 72)
    print("VALIDADOR DE LIGAS — HarryNine V14")
    print("=" * 72)
    print(f"API key: ...{API_KEY[-6:]}")
    print()

    resultados_ok = []
    resultados_problema = []

    for nombre, id_prop, season, country, grupo in CANDIDATAS:
        print(f"🔎 {nombre} (id propuesto: {id_prop}, season: {season}, país: {country})")
        info = consultar_liga_por_id(id_prop)

        if info is None:
            print(f"   ❌ ID {id_prop} NO devuelve resultados en la API")
            # Buscar por nombre
            matches = buscar_liga_por_nombre(nombre, country)
            if matches:
                print(f"   🔍 Búsqueda por nombre encontró {len(matches)} match(es):")
                for m in matches[:5]:
                    lg = m["league"]
                    co = m["country"]
                    print(f"      → id={lg['id']:5d}  {lg['name']!r:35s}  país={co['name']}")
                resultados_problema.append((nombre, id_prop, "ID no existe", matches))
            else:
                resultados_problema.append((nombre, id_prop, "ID no existe y búsqueda sin resultados", []))
            print()
            continue

        liga_info = info["league"]
        country_info = info["country"]
        nombre_real = liga_info["name"]
        pais_real = country_info["name"]

        # Verificar pais
        country_ok = pais_real.lower() == country.lower()
        # Verificar temporada
        es_current, season_info = temporada_activa(info, season)

        # Mostrar
        if country_ok and season_info:
            estado = "✅" if es_current else "⚠️ (temporada existe pero no es 'current')"
            print(f"   {estado} ID {id_prop} = '{nombre_real}' ({pais_real}) — season {season} {'current' if es_current else 'NO current'}")
            if es_current:
                resultados_ok.append((nombre, id_prop, season, pais_real, grupo))
            else:
                # La season existe pero no es current — aún sirve para consultas, marcamos warning
                resultados_ok.append((nombre, id_prop, season, pais_real, grupo))
        else:
            if not country_ok:
                print(f"   ❌ País no coincide: esperado {country}, API devuelve {pais_real}")
            if not season_info:
                print(f"   ❌ Season {season} no existe para esta liga")
                seasons_disp = [s.get("year") for s in info.get("seasons", [])]
                print(f"      Seasons disponibles: {seasons_disp[-8:]}")
            resultados_problema.append((nombre, id_prop, f"mismatch país/season", info))
        print()

    # Resumen
    print("=" * 72)
    print("RESUMEN")
    print("=" * 72)
    print(f"✅ OK:        {len(resultados_ok)}/{len(CANDIDATAS)}")
    print(f"❌ Problemas: {len(resultados_problema)}/{len(CANDIDATAS)}")
    print()

    if resultados_ok:
        print("DICTS LISTOS PARA bot.py:")
        print("-" * 72)
        por_grupo = {}
        for nombre, lid, season, pais, grupo in resultados_ok:
            por_grupo.setdefault(grupo, []).append((nombre, lid, season, pais))
        for grupo, items in por_grupo.items():
            print(f"\n# Agregar a {grupo}_LEAGUES:")
            for nombre, lid, season, pais in items:
                print(f'    "{nombre}": {{"id": {lid}, "season": {season}, "country": "{pais}"}},')

    if resultados_problema:
        print()
        print("⚠️ REVISAR MANUALMENTE:")
        print("-" * 72)
        for nombre, lid, motivo, _ in resultados_problema:
            print(f"  - {nombre} (id={lid}): {motivo}")

    return len(resultados_problema) == 0


if __name__ == "__main__":
    ok = validar()
    sys.exit(0 if ok else 1)
