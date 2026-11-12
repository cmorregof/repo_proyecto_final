# preguntar.py  ---  preguntas conceptuales con citas (R1) o "no lo se" (R2)
# Uso:  python3 preguntar.py "Que diferencia hay entre rule y erule?"
import os, re, sys

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(AQUI, "..", "..", "semana1", "taller"))

from modelo import preguntar, CONFIG
from utilidades import registrar
from buscar import cargar, donde
from rag import contexto_citable

K = 5
SISTEMA = (
    "Eres un asistente del curso de Razonamiento Automatico (logica e Isabelle). "
    "Responde en espanol usando SOLO los fragmentos que te doy. Despues de cada "
    "afirmacion pon la etiqueta del fragmento que la respalda, por ejemplo [F2]. "
    "Si los fragmentos no bastan, dilo con estas palabras: 'Los documentos no lo "
    "respaldan.' Si agregas algo de conocimiento general, advierte que no viene "
    "de los documentos. Nunca inventes etiquetas. Si la pregunta no es de logica "
    "o de Isabelle, declinala.")


def etiquetas(texto):
    return {int(x) for x in re.findall(r"\[F(\d+)\]", texto)}


def responder(pregunta):
    frags = cargar().buscar(pregunta, K)
    msgs = [{"role": "system", "content": SISTEMA},
            {"role": "user", "content": f"Fragmentos:\n\n{contexto_citable(frags)}\n\n"
                                        f"Pregunta: {pregunta}"}]
    respuesta = preguntar(msgs)
    usadas = etiquetas(respuesta)
    inventadas = sorted(usadas - set(range(1, len(frags) + 1)))   # lo revisa el codigo,
    registrar("registros/conceptual.jsonl", pregunta=pregunta,    # no la buena fe del modelo
              modelo=CONFIG["modelo"], pasajes=[donde(f) for f in frags],
              prompt=msgs, respuesta=respuesta, inventadas=inventadas)
    return respuesta, frags, usadas, inventadas


if __name__ == "__main__":
    os.makedirs("registros", exist_ok=True)
    respuesta, frags, usadas, inventadas = responder(" ".join(sys.argv[1:]))
    print(respuesta)
    print("\nFuentes")
    for j in sorted(usadas):
        if 1 <= j <= len(frags):
            print(f"  [F{j}] {donde(frags[j-1])}")
    if inventadas:
        print(f"\n!! CITA INVENTADA: {', '.join(f'[F{j}]' for j in inventadas)} "
              "no corresponde a ningun fragmento. Esta respuesta no se puede mostrar asi.")
    if not usadas and "no lo respaldan" not in respuesta:
        print("\n!! La respuesta no cita nada y tampoco admite que no sabe.")
