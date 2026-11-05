# prompt.py  ---  armar la pregunta para el modelo
SISTEMA = ("Eres un experto en Isabelle/Isar. Responde SOLO con la "
           "demostracion que va despues del enunciado, sin repetirlo.")


def instruccion_estilo(p):
    if p["estilo"] == "dn":
        return ("Usa solo deduccion natural: rule, erule, assumption, '..'. "
                "Prohibido auto, simp, blast y similares.")
    return "Puedes usar cualquier metodo."


def pedir_mensajes(p, extra=""):
    """extra: vacio en la configuracion 1; la semana 2 ahi van los pasajes recuperados."""
    usuario = (f"Contexto de la teoria:\n{p['contexto']}\n\n"
               f"{extra}"
               f"Enunciado:\n{p['enunciado']}\n\n"
               f"{instruccion_estilo(p)}")
    return [{"role": "system", "content": SISTEMA},
            {"role": "user",   "content": usuario}]
