# normalizar.py  ---  una sola forma para los simbolos
# En los .thy se escribe \<and>; en los PDF y en las preguntas, el simbolo.
# Antes de indexar Y antes de buscar, todo pasa a palabras comunes.
import re

SIMBOLOS = {
    "and":            ["\\<and>", "∧"],              # conjuncion
    "or":             ["\\<or>", "∨"],               # disyuncion
    "not":            ["\\<not>", "¬"],              # negacion
    "implies":        ["\\<longrightarrow>", "⟶", "-->"],
    "entails":        ["\\<Longrightarrow>", "⟹", "==>",
                       "\\<turnstile>", "⊢"],        # |- de los enunciados
    "iff":            ["\\<longleftrightarrow>", "⟷"],
    "forall":         ["\\<forall>", "∀"],
    "exists":         ["\\<exists>", "∃"],
    "false":          ["\\<bottom>", "⊥"],
}

TABLA = [(s, f" {palabra} ") for palabra, formas in SIMBOLOS.items() for s in formas]


def normalizar(texto):
    for simbolo, palabra in TABLA:
        texto = texto.replace(simbolo, palabra)
    texto = re.sub(r"\\<([A-Za-z]+)>", r" \1 ", texto)    # el resto: \<lbrakk> -> lbrakk
    return texto.lower()
