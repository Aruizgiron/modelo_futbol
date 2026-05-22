"""
corregir_fixture_ids.py
HarryNine V14 — Corrige los fixture_id sinteticos de los picks reconstruidos.

Los picks reconstruidos tienen fixture_id tipo "REC-xxxxx" (sinteticos).
El bot no puede cerrarlos porque la API no reconoce esos IDs.

Este script:
1. Toma cada pick con fixture_id que empieza por "REC-" y estado "pendiente".
2. Busca el partido real en la API por nombres de equipos + fecha.
3. Si lo encuentra, reemplaza el fixture_id sintetico por el real.
4. Tras esto, actualizar_resultados_automaticos() del bot ya puede cerrarlos.

No cierra los picks: solo corrige el ID. El cierre lo hace el bot despues
(con /rendimiento o el job automatico check_combinadas).

Uso:  venv/bin/python corregir_fixture_ids.py
"""
import json
import os
import shutil
import time
import unicodedata
from datetime import datetime

import requests

BOT_DIR = os.path.dirname(os.path.abspath(__file__))
PICKS_FILE = os.path.join(BOT_DIR, "picks_guardados.json")

API_KEY = "3016c710cf4d9ca6f30f82eabefb7bd4"
BASE_URL = "https://v3.football.api-sports.io"
HEADERS = {"x-apisports-key": API_KEY}


def normalizar(texto):
    """Quita acentos y pasa a minusculas para comparar nombres de equipos."""
    if not texto:
        return ""
    t = unicodedata.normalize("NFKD", str(texto))
    t = "".join(c for c in t if not unicodedata.combining(c))
    return t.lower().strip()


def equipos_de_partido(partido):
    """Separa 'Equipo A vs Equipo B' en (A, B)."""
    if " vs " in partido:
        a, b = partido.split(" vs ", 1)
        return normalizar(a), normalizar(b)
    return normalizar(partido), ""


def buscar_fixture_real(partido, fecha):
    """
    Busca en la API el fixture real de un partido en una fecha dada.
    Devuelve el fixture_id real o None.
    """
    home_n, away_n = equipos_de_partido(partido)
    try:
        r = requests.get(f"{BASE_URL}/fixtures", headers=HEADERS,
                         params={"date": fecha, "timezone": "America/Lima"},
                         timeout=20)
        r.raise_for_status()
        data = r.json()
    except Exception as e:
        print(f"    error API: {e}")
        return None

    mejor = None
    for fx in data.get("response", []):
        h = normalizar(fx["teams"]["home"]["name"])
        a = normalizar(fx["teams"]["away"]["name"])
        # Match flexible: que el nombre del equipo del pick este contenido
        # en el de la API o viceversa (maneja abreviaturas)
        home_ok = home_n in h or h in home_n or _palabras_comunes(home_n, h)
        away_ok = away_n in a or a in away_n or _palabras_comunes(away_n, a)
        if home_ok and away_ok:
            return str(fx["fixture"]["id"])
    return mejor


def _palabras_comunes(n1, n2):
    """True si comparten alguna palabra significativa (>3 letras)."""
    p1 = {w for w in n1.split() if len(w) > 3}
    p2 = {w for w in n2.split() if len(w) > 3}
    return bool(p1 & p2)


def main():
    print("=" * 60)
    print("CORRECCION DE FIXTURE_IDs SINTETICOS")
    print("=" * 60)

    with open(PICKS_FILE, "r", encoding="utf-8") as f:
        picks = json.load(f)

    # Backup
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    bkp = os.path.join(BOT_DIR, "backups")
    os.makedirs(bkp, exist_ok=True)
    shutil.copy(PICKS_FILE, os.path.join(bkp, f"picks_{ts}.json"))
    print(f"Backup en backups/picks_{ts}.json\n")

    # Picks a corregir: fixture_id sintetico + pendiente
    objetivo = [p for p in picks
                if str(p.get("fixture_id", "")).startswith("REC-")
                and p.get("estado") == "pendiente"]

    print(f"Picks reconstruidos pendientes a corregir: {len(objetivo)}")
    print()

    # Cache de busquedas: (partido, fecha) -> fixture_id real
    cache = {}
    corregidos = 0
    no_encontrados = 0

    for p in objetivo:
        partido = p.get("partido", "")
        fecha = p.get("fecha_partido") or p.get("fecha", "")
        clave = (partido, fecha)

        if clave in cache:
            real_id = cache[clave]
        else:
            print(f"  buscando: {partido}  ({fecha})")
            real_id = buscar_fixture_real(partido, fecha)
            cache[clave] = real_id
            time.sleep(0.4)  # no saturar la API

        if real_id:
            p["fixture_id"] = real_id
            corregidos += 1
        else:
            no_encontrados += 1
            print(f"    -> NO encontrado en API")

    # Guardar atomico
    tmp = PICKS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(picks, f, indent=2, ensure_ascii=False)
    os.replace(tmp, PICKS_FILE)

    print()
    print("=" * 60)
    print("RESULTADO")
    print("=" * 60)
    print(f"  fixture_id corregidos:  {corregidos}")
    print(f"  no encontrados en API:  {no_encontrados}")
    print()
    print("Ahora usa /rendimiento en Telegram (o espera el job de 15 min):")
    print("el bot cerrara automaticamente estos picks y sus combinadas.")


if __name__ == "__main__":
    main()
