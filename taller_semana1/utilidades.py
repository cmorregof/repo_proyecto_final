# utilidades.py  ---  limpiar la respuesta y dejar registro (R5)
import json, re, time


def extraer_prueba(texto):
    m = re.search(r"```(?:isabelle|isar)?\s*\n(.*?)```", texto, re.S)
    return (m.group(1) if m else texto).strip()


def registrar(archivo, **datos):
    datos["hora"] = time.strftime("%Y-%m-%d %H:%M:%S")
    with open(archivo, "a", encoding="utf-8") as f:    # "a" = agregar, nunca borrar
        f.write(json.dumps(datos, ensure_ascii=False) + "\n")
