# medir_recuperacion.py  ---  ¿la busqueda encuentra la solucion? (sin modelo)
# Para cada ejercicio de R1, la solucion esta en R1_Deduccion_natural.thy con
# el nombre ejercicio_N_algo. Contamos en que puesto aparece.
# Uso:  python3 medir_recuperacion.py        (las 58)
import json, os, sys
from buscar import cargar
from rag import consulta_de, solo_demostraciones

AQUI = os.path.dirname(os.path.abspath(__file__))
BENCH = os.path.join(AQUI, "..", "..", "Recursos", "benchmark_R1.json")
SOLUCIONES = "R1_Deduccion_natural.thy"

indice = cargar()
preguntas = json.load(open(BENCH, encoding="utf-8"))
puestos = []
for p in preguntas:
    n = p["id"].split("_")[-1]                       # R1/ejercicio_12 -> 12
    hallados = indice.buscar(consulta_de(p), 10, filtro=solo_demostraciones)
    puesto = next((i for i, f in enumerate(hallados, 1)
                   if f["fuente"].endswith(SOLUCIONES)
                   and f["nombre"].startswith(f"ejercicio_{n}_")), None)
    puestos.append(puesto)
    if "-v" in sys.argv:
        print(f"{p['id']:<18} puesto {puesto or '-'}   primero: {hallados[0]['nombre'] if hallados else '-'}")

N = len(preguntas)
for k in (1, 3, 5, 10):
    aciertos = sum(1 for x in puestos if x and x <= k)
    print(f"la solucion esta entre los primeros {k:>2}: {aciertos:>2}/{N}  ({100*aciertos/N:.0f}%)")
