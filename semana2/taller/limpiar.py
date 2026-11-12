# limpiar.py  ---  extraer_prueba, version 2
# Con recuperacion aparece un error nuevo: el modelo COPIA el fragmento entero,
# con su bloque text, la linea del lema y a veces el lema siguiente. Para
# evaluar.py eso es trampa (trae 'lemma'). Nos quedamos con la primera
# demostracion y cortamos donde empieza otro comando.
import re

ABRE   = re.compile(r"(?:^|(?<=\s))(proof|by|using|apply|unfolding)\b|^\s*(from|have|show)\b", re.M)
CIERRA = re.compile(r"^\s*(lemma|theorem|corollary|text|section|subsection|end\s*$|oops)\b", re.M)


def extraer_prueba(texto):
    m = re.search(r"```[a-zA-Z]*\s*\n(.*?)```", texto, re.S)
    t = (m.group(1) if m else texto).strip()
    a = ABRE.search(t)
    if not a:
        return ""                               # no hay demostracion: mejor vacio que basura
    t = t[a.start():].lstrip()
    c = CIERRA.search(t, 1)                     # lo que venga despues no es de esta prueba
    return (t[:c.start()] if c else t).strip()
