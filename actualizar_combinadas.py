"""
Script independiente para actualizar resultados de combinadas.json
Ejecucion: python actualizar_combinadas.py
"""
import json, requests, os, sys
from datetime import datetime

# Configuracion
API_KEY = None  # Se lee del bot.py automaticamente
BOT_DIR = os.path.dirname(os.path.abspath(__file__))
COMBINADAS_FILE = os.path.join(BOT_DIR, "combinadas.json")
PICKS_FILE = os.path.join(BOT_DIR, "picks_guardados.json")

# Intentar leer API key del .env
try:
    env_path = os.path.join(BOT_DIR, ".env")
    with open(env_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line.startswith("API_FOOTBALL_KEY"):
                API_KEY = line.split("=", 1)[-1].strip().strip('"').strip("'")
                break
    if API_KEY:
        print(f"API key encontrada en .env")
except Exception as e:
    print(f"No se pudo leer .env: {e}")

if not API_KEY:
    API_KEY = input("Ingresa tu API_FOOTBALL_KEY: ").strip()

HEADERS = {
    "x-apisports-key": API_KEY,
}

def api_get(endpoint):
    try:
        url = f"https://v3.football.api-sports.io{endpoint}"
        r = requests.get(url, headers=HEADERS, timeout=15)
        data = r.json()
        return data.get("response", [])
    except Exception as e:
        print(f"  API error: {e}")
        return []

def evaluar_jugada(jugada, gh, ga, corners=None, tarjetas=None):
    total = gh + ga
    if "Under 3.5" in jugada: return total <= 3
    if "Under 2.5" in jugada: return total <= 2
    if "Over 2.5" in jugada: return total >= 3
    if "Over 1.5" in jugada: return total >= 2
    if "Over 0.5" in jugada: return total >= 1
    if "Ambos marcan" in jugada: return gh > 0 and ga > 0
    if "1X" in jugada: return gh >= ga
    if "X2" in jugada: return ga >= gh
    if "12" in jugada: return gh != ga
    if corners is not None:
        import re
        m = re.search(r"(\d+\.?\d*)", jugada.split("Over")[-1]) if "Over" in jugada else None
        if m:
            linea = float(m.group(1))
            return corners > linea
    if tarjetas is not None:
        import re
        m = re.search(r"(\d+\.?\d*)", jugada.split("Over")[-1]) if "Over" in jugada else None
        if m:
            linea = float(m.group(1))
            return tarjetas > linea
    return None

def get_stats(fixture_id):
    stats = api_get(f"/fixtures/statistics?fixture={fixture_id}")
    corners = 0
    tarjetas = 0
    for team in stats:
        for item in team.get("statistics", []):
            tipo = item.get("type","")
            try:
                val = int(str(item.get("value") or 0).replace("%","").strip() or 0)
            except:
                val = 0
            if tipo == "Corner Kicks": corners += val
            elif tipo == "Yellow Cards": tarjetas += val
            elif tipo == "Red Cards": tarjetas += val * 2
    return corners, tarjetas

def main():
    print(f"\n{'='*60}")
    print("ACTUALIZADOR DE COMBINADAS — HarryNine V14")
    print(f"{'='*60}\n")

    # Cargar archivos
    with open(COMBINADAS_FILE, "r", encoding="utf-8") as f:
        combinadas = json.load(f)
    
    try:
        with open(PICKS_FILE, "r", encoding="utf-8") as f:
            picks = json.load(f)
    except:
        picks = []

    # Indice de picks por fixture_id y partido+jugada
    idx_fid = {str(p.get("fixture_id","")): p for p in picks}
    idx_pj = {f"{p.get('partido','')}|{p.get('jugada','')}": p for p in picks}

    cambios = 0
    for i, c in enumerate(combinadas):
        if c.get("estado") not in ("pendiente", None) and c.get("estado") != "pendiente":
            continue
        if c.get("sin_combinada"):
            continue

        print(f"Combinada {i+1}: {c.get('subtipo','?').upper()} | Cuota: {c.get('cuota_combinada','?')}x | Ticket: {c.get('ticket_id','sin ticket')}")
        
        picks_c = c.get("picks", [])
        estados_picks = []

        for j, pick_c in enumerate(picks_c):
            fid = str(pick_c.get("fixture_id",""))
            jugada = pick_c.get("jugada","")
            partido = pick_c.get("partido","")
            clave_pj = f"{partido}|{jugada}"

            print(f"  Pick {j+1}: {partido} | {jugada}")

            # Buscar en picks_guardados primero
            p_saved = idx_fid.get(fid) or idx_pj.get(clave_pj)
            if p_saved and p_saved.get("estado","").lower() in ("acierto","fallo"):
                estado_p = p_saved["estado"].lower()
                pick_c["estado"] = estado_p
                pick_c["resultado_real"] = p_saved.get("resultado_real","")
                print(f"    -> {estado_p.upper()} (desde picks_guardados): {pick_c['resultado_real']}")
                estados_picks.append(estado_p)
                continue

            # Consultar API
            if not fid:
                print(f"    -> Sin fixture_id, saltando")
                estados_picks.append("pendiente")
                continue

            fx = api_get(f"/fixtures?id={fid}")
            if not fx:
                print(f"    -> No se encontro fixture {fid}")
                estados_picks.append("pendiente")
                continue

            status = fx[0]["fixture"]["status"]["short"]
            if status not in ("FT","AET","PEN"):
                print(f"    -> Partido no finalizado (status: {status})")
                estados_picks.append("pendiente")
                continue

            gh = fx[0]["goals"]["home"] or 0
            ga = fx[0]["goals"]["away"] or 0
            print(f"    -> Partido finalizado: {gh}-{ga}")

            corners, tarjetas = None, None
            if "Corner" in jugada or "Tarjeta" in jugada:
                corners, tarjetas = get_stats(fid)
                print(f"    -> Corners: {corners} | Tarjetas: {tarjetas}")

            acierto = evaluar_jugada(jugada, gh, ga, corners, tarjetas)

            if acierto is True:
                pick_c["estado"] = "acierto"
                if "Corner" in jugada:
                    pick_c["resultado_real"] = f"{corners} corners"
                elif "Tarjeta" in jugada:
                    pick_c["resultado_real"] = f"{tarjetas} tarjetas"
                else:
                    pick_c["resultado_real"] = f"{gh}-{ga}"
                print(f"    -> ACIERTO: {pick_c['resultado_real']}")
                estados_picks.append("acierto")
            elif acierto is False:
                pick_c["estado"] = "fallo"
                if "Corner" in jugada:
                    pick_c["resultado_real"] = f"{corners} corners"
                elif "Tarjeta" in jugada:
                    pick_c["resultado_real"] = f"{tarjetas} tarjetas"
                else:
                    pick_c["resultado_real"] = f"{gh}-{ga}"
                print(f"    -> FALLO: {pick_c['resultado_real']}")
                estados_picks.append("fallo")
            else:
                print(f"    -> No se pudo evaluar la jugada")
                estados_picks.append("pendiente")

        # Actualizar estado de la combinada
        cerrados = [e for e in estados_picks if e in ("acierto","fallo")]
        if len(cerrados) == len(picks_c):
            if all(e == "acierto" for e in estados_picks):
                c["estado"] = "acierto"
                print(f"  => COMBINADA: ACIERTO")
            else:
                c["estado"] = "fallo"
                for k, e in enumerate(estados_picks):
                    if e == "fallo":
                        c["fallo_en"] = picks_c[k].get("partido","")
                        break
                print(f"  => COMBINADA: FALLO (fallo en: {c.get('fallo_en','')})")
            cambios += 1
        else:
            print(f"  => COMBINADA: aun PENDIENTE ({len(cerrados)}/{len(picks_c)} cerrados)")
        print()

    # Guardar
    with open(COMBINADAS_FILE, "w", encoding="utf-8") as f:
        json.dump(combinadas, f, ensure_ascii=False, indent=2)

    print(f"\n{'='*60}")
    print(f"Completado. Combinadas actualizadas: {cambios}")
    print(f"Archivo guardado: {COMBINADAS_FILE}")
    print(f"{'='*60}\n")

if __name__ == "__main__":
    main()
