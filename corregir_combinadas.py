"""
Script de correccion de combinadas.json
Reevalua todos los picks usando la API y corrige aciertos/fallos mal marcados.
Ejecucion: python corregir_combinadas.py
"""
import json, requests, os, re
from datetime import datetime

BOT_DIR = os.path.dirname(os.path.abspath(__file__))
COMBINADAS_FILE = os.path.join(BOT_DIR, "combinadas.json")

# Leer API key del .env
API_KEY = None
try:
    with open(os.path.join(BOT_DIR, ".env"), "r") as f:
        for line in f:
            if "API_FOOTBALL_KEY" in line:
                API_KEY = line.split("=",1)[-1].strip().strip('"').strip("'")
                break
except:
    pass
if not API_KEY:
    API_KEY = input("API_FOOTBALL_KEY: ").strip()

HEADERS = {"x-apisports-key": API_KEY}

def api_get(endpoint):
    try:
        r = requests.get(f"https://v3.football.api-sports.io{endpoint}",
                        headers=HEADERS, timeout=15)
        return r.json().get("response", [])
    except Exception as e:
        print(f"  API error: {e}")
        return []

def get_stats(fixture_id):
    stats = api_get(f"/fixtures/statistics?fixture={fixture_id}")
    corners, tarjetas = 0, 0
    for team in stats:
        for item in team.get("statistics", []):
            tipo = item.get("type","")
            try: val = int(str(item.get("value") or 0).replace("%","").strip() or 0)
            except: val = 0
            if tipo == "Corner Kicks": corners += val
            elif tipo == "Yellow Cards": tarjetas += val
            elif tipo == "Red Cards": tarjetas += val * 2
    return corners, tarjetas

def evaluar(jugada, gh, ga, corners, tarjetas):
    jugada_l = jugada.lower()
    total = gh + ga

    def linea(txt):
        m = re.search(r"(\d+\.?\d*)", txt)
        return float(m.group(1)) if m else None

    if "under" in jugada_l and "gol" in jugada_l:
        l = linea(jugada); return total < l if l else None
    elif "over" in jugada_l and "gol" in jugada_l:
        l = linea(jugada); return total > l if l else None
    elif "ambos marcan" in jugada_l or "btts" in jugada_l:
        if "no" in jugada_l: return not (gh > 0 and ga > 0)
        return gh > 0 and ga > 0
    elif "corner" in jugada_l and "over" in jugada_l:
        l = linea(jugada.split("Over")[-1]); return corners > l if l else None
    elif "corner" in jugada_l and "under" in jugada_l:
        l = linea(jugada.split("Under")[-1]); return corners < l if l else None
    elif "tarjeta" in jugada_l and "over" in jugada_l:
        l = linea(jugada.split("Over")[-1]); return tarjetas > l if l else None
    elif "tarjeta" in jugada_l and "under" in jugada_l:
        l = linea(jugada.split("Under")[-1]); return tarjetas < l if l else None
    elif "1x" in jugada_l: return gh >= ga
    elif "x2" in jugada_l: return ga >= gh
    elif jugada_l.strip() == "1": return gh > ga
    elif jugada_l.strip() == "2": return ga > gh
    elif jugada_l.strip() == "x" or "empate" in jugada_l: return gh == ga
    elif "12" in jugada_l: return gh != ga
    return None

def main():
    with open(COMBINADAS_FILE, "r", encoding="utf-8") as f:
        combinadas = json.load(f)

    cambios_total = 0

    # Asignar ticket_id a combinadas que no lo tienen
    import uuid
    for c in combinadas:
        if not c.get("ticket_id") and not c.get("sin_combinada"):
            subtipo = c.get("subtipo","pre")[:3].upper()
            fecha_c = (c.get("fecha") or "").replace("-","")[2:]
            c["ticket_id"] = f"COMB-{subtipo}-{fecha_c}-{str(uuid.uuid4())[:6].upper()}"
            print(f"Ticket asignado: {c['ticket_id']}")

    for i, c in enumerate(combinadas):
        if c.get("sin_combinada"):
            continue

        picks_c = c.get("picks", [])
        estados = []
        cambio_en_comb = False

        print(f"\nCombinada {i+1}: [{c.get('subtipo','?').upper()}] "
              f"Cuota:{c.get('cuota_combinada','?')}x | "
              f"Estado actual: {c.get('estado','?')}")

        for pick_c in picks_c:
            fid = str(pick_c.get("fixture_id",""))
            jugada = pick_c.get("jugada","")
            partido = pick_c.get("partido","")

            # Consultar API
            fx = api_get(f"/fixtures?id={fid}")
            if not fx:
                print(f"  ? {partido} | Sin datos API")
                estados.append(pick_c.get("estado","pendiente"))
                continue

            status = fx[0]["fixture"]["status"]["short"]
            if status not in ("FT","AET","PEN"):
                print(f"  ⏳ {partido} | No finalizado ({status})")
                estados.append("pendiente")
                continue

            gh = fx[0]["goals"]["home"] or 0
            ga = fx[0]["goals"]["away"] or 0
            corners, tarjetas = get_stats(fid)

            acierto = evaluar(jugada, gh, ga, corners, tarjetas)

            if "corner" in jugada.lower():
                resultado_str = f"{corners} corners"
            elif "tarjeta" in jugada.lower():
                resultado_str = f"{tarjetas} tarjetas"
            else:
                resultado_str = f"{gh}-{ga}"

            if acierto is True:
                nuevo_estado = "acierto"
            elif acierto is False:
                nuevo_estado = "fallo"
            else:
                nuevo_estado = "pendiente"
                print(f"  ? {partido} | {jugada} | No se pudo evaluar")
                estados.append("pendiente")
                continue

            estado_anterior = pick_c.get("estado","pendiente")
            pick_c["estado"] = nuevo_estado
            pick_c["resultado_real"] = resultado_str

            emoji = "✅" if nuevo_estado == "acierto" else "❌"
            cambio_str = f" ← CORREGIDO (era {estado_anterior})" if estado_anterior != nuevo_estado else ""
            print(f"  {emoji} {partido} | {jugada} | {resultado_str}{cambio_str}")

            if estado_anterior != nuevo_estado:
                cambio_en_comb = True
                cambios_total += 1

            estados.append(nuevo_estado)

        # Recalcular estado combinada
        cerrados = [e for e in estados if e in ("acierto","fallo")]
        if len(cerrados) == len(picks_c) and picks_c:
            nuevo_estado_comb = "acierto" if all(e=="acierto" for e in estados) else "fallo"
            fallo_pick = ""
            if nuevo_estado_comb == "fallo":
                for j, e in enumerate(estados):
                    if e == "fallo":
                        fallo_pick = picks_c[j].get("partido","")
                        break

            estado_anterior_comb = c.get("estado","pendiente")
            c["estado"] = nuevo_estado_comb
            if fallo_pick:
                c["fallo_en"] = fallo_pick
            elif nuevo_estado_comb == "acierto":
                c.pop("fallo_en", None)

            if estado_anterior_comb != nuevo_estado_comb:
                emoji_c = "✅" if nuevo_estado_comb == "acierto" else "❌"
                print(f"  => COMBINADA: {emoji_c} {nuevo_estado_comb.upper()} "
                      f"(era {estado_anterior_comb})"
                      + (f" | Fallo: {fallo_pick}" if fallo_pick else ""))
            else:
                print(f"  => COMBINADA: Sin cambio ({nuevo_estado_comb})")
        elif picks_c:
            print(f"  => COMBINADA: Aun PENDIENTE ({len(cerrados)}/{len(picks_c)} cerrados)")

    with open(COMBINADAS_FILE, "w", encoding="utf-8") as f:
        json.dump(combinadas, f, ensure_ascii=False, indent=2)

    print(f"\n{'='*60}")
    print(f"Correcciones aplicadas: {cambios_total} picks")
    print(f"Archivo guardado: {COMBINADAS_FILE}")
    print(f"{'='*60}")

if __name__ == "__main__":
    main()
