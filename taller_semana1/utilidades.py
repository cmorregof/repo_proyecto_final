# utilidades.py  ---  limpiar la respuesta y dejar registro (R5)
import json, re, time


INICIO = re.compile(r"^\s*(proof|by|using|apply|from|unfolding)\b", re.M)


def extraer_prueba(texto):
    m = re.search(r"```(?:isabelle|isar)?\s*\n(.*?)```", texto, re.S)
    t = (m.group(1) if m else texto).strip()
    if re.match(r"\s*(lemma|theorem)\b", t):   # el modelo repitio el enunciado
        k = INICIO.search(t)
        t = t[k.start():] if k else ""
    return re.sub(r"\boops\s*$", "", t).strip()   # y a veces cierra con oops


def registrar(archivo, **datos):
    datos["hora"] = time.strftime("%Y-%m-%d %H:%M:%S")
    with open(archivo, "a", encoding="utf-8") as f:    # "a" = agregar, nunca borrar
        f.write(json.dumps(datos, ensure_ascii=False) + "\n")
