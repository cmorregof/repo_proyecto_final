# config2.py  ---  configuracion 2: el modelo con recuperacion, sin verificacion
# Uso:  python3 config2.py        (las 58)
#       python3 config2.py 3      (solo las 3 primeras, para probar)
# Antes:  python3 indexar.py      (una sola vez; crea indice.json)
import json, os, sys

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(AQUI, "..", "..", "semana1", "taller"))   # lo de la semana 1

from modelo import preguntar, CONFIG          # el MISMO modelo de la configuracion 1
from utilidades import registrar
from limpiar import extraer_prueba          # version 2: tambien quita fragmentos copiados
from prompt import pedir_mensajes
from buscar import cargar, donde
from rag import pasajes_para, extra_para_demostrar

BENCH = os.path.join(AQUI, "..", "..", "Recursos", "benchmark_R1.json")
K = 3                                         # cuantos pasajes se le dan al modelo
os.makedirs("registros", exist_ok=True)

indice = cargar()
preguntas = json.load(open(BENCH, encoding="utf-8"))
if len(sys.argv) > 1:
    preguntas = preguntas[:int(sys.argv[1])]

respuestas = {}
for i, p in enumerate(preguntas, 1):
    frags  = pasajes_para(p, indice, K)
    msgs   = pedir_mensajes(p, extra=extra_para_demostrar(frags))
    try:
        crudo = preguntar(msgs)
    except Exception as e:                    # timeout, modelo apagado...: se anota y se sigue
        crudo = f"ERROR: {e}"
    prueba = extraer_prueba(crudo)
    respuestas[p["id"]] = prueba
    registrar("registros/config2.jsonl", id=p["id"], modelo=CONFIG["modelo"],
              pasajes=[{"donde": donde(f), "puntaje": f["puntaje"]} for f in frags],
              prompt=msgs, crudo=crudo, prueba=prueba)          # R5: tambien los pasajes
    print(f"[{i}/{len(preguntas)}] {p['id']}   <- {donde(frags[0]) if frags else 'sin pasajes'}")

json.dump(respuestas, open("respuestas_config2.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print("Listo: respuestas_config2.json")
