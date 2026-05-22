"""
diagnostico_picks_dias.py
Revisa picks_guardados.json y muestra cuantos picks hay por dia,
para detectar dias sin registros.
"""
import json
import os

# Buscar el archivo de picks
posibles = [
    "picks_guardados.json",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "picks_guardados.json"),
]
PICKS_FILE = None
for p in posibles:
    if os.path.exists(p):
        PICKS_FILE = p
        break

if not PICKS_FILE:
    print("❌ No se encontro picks_guardados.json")
    raise SystemExit(1)

with open(PICKS_FILE, "r", encoding="utf-8") as f:
    picks = json.load(f)

print("=" * 60)
print(f"DIAGNOSTICO DE PICKS — {PICKS_FILE}")
print("=" * 60)
print(f"Total de picks en el archivo: {len(picks)}")
print()

# Agrupar por fecha
por_dia = {}
for p in picks:
    fecha = (p.get("fecha_partido") or p.get("fecha") or "SIN_FECHA")[:10]
    por_dia.setdefault(fecha, {"total": 0, "acierto": 0, "fallo": 0,
                               "pendiente": 0, "tipos": {}})
    por_dia[fecha]["total"] += 1
    estado = p.get("estado", "pendiente").lower()
    if estado in ("acierto", "fallo", "pendiente"):
        por_dia[fecha][estado] += 1
    else:
        por_dia[fecha]["pendiente"] += 1
    tipo = p.get("tipo", "?")
    por_dia[fecha]["tipos"][tipo] = por_dia[fecha]["tipos"].get(tipo, 0) + 1

print("PICKS POR DIA (mayo 2026):")
print("-" * 60)
for fecha in sorted(por_dia.keys()):
    if not fecha.startswith("2026-05"):
        continue
    d = por_dia[fecha]
    tipos_str = ", ".join(f"{k}:{v}" for k, v in d["tipos"].items())
    print(f"  {fecha}: {d['total']:3d} picks "
          f"(✅{d['acierto']} ❌{d['fallo']} ⏳{d['pendiente']}) "
          f"[{tipos_str}]")

# Detectar dias faltantes en el rango
print()
print("DIAS FALTANTES EN MAYO (15 al 22):")
print("-" * 60)
faltantes = []
for dia in range(15, 23):
    fecha = f"2026-05-{dia:02d}"
    if fecha not in por_dia:
        faltantes.append(fecha)
        print(f"  ❌ {fecha}: SIN PICKS REGISTRADOS")
    else:
        print(f"  ✅ {fecha}: {por_dia[fecha]['total']} picks")

if faltantes:
    print()
    print(f"⚠️  {len(faltantes)} dia(s) sin picks: {', '.join(faltantes)}")
