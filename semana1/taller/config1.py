# config1.py  ---  configuracion 1: solo el modelo (la linea base)
# Uso:  python3 config1.py        (las 58)
#       python3 config1.py 3      (solo las 3 primeras, para probar)
import json, os, sys
from modelo import preguntar, CONFIG
from utilidades import extraer_prueba, registrar
from prompt import pedir_mensajes

BENCH = os.path.join(os.path.dirname(__file__), "..", "..", "Recursos", "benchmark_R1.json")
os.makedirs("registros", exist_ok=True)

preguntas = json.load(open(BENCH, encoding="utf-8"))
if len(sys.argv) > 1:
    preguntas = preguntas[:int(sys.argv[1])]

respuestas = {}
for i, p in enumerate(preguntas, 1):
    msgs   = pedir_mensajes(p)
    try:
        crudo = preguntar(msgs)
    except Exception as e:                    # timeout, modelo apagado...: se anota y se sigue
        crudo = f"ERROR: {e}"
    prueba = extraer_prueba(crudo)
    respuestas[p["id"]] = prueba
    registrar("registros/config1.jsonl", id=p["id"], modelo=CONFIG["modelo"],
              prompt=msgs, crudo=crudo, prueba=prueba)
    print(f"[{i}/{len(preguntas)}] {p['id']}")

json.dump(respuestas, open("respuestas_config1.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print("Listo: respuestas_config1.json")
