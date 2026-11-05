#!/usr/bin/env python3
"""Evalúa las respuestas de un asistente sobre un benchmark.

Entrada:
  benchmark.json   preguntas (ver construir_benchmark.py)
  respuestas.json  { "R1/ejercicio_1": "<demostración>", ... }
                   La demostración es solo lo que va DESPUÉS del enunciado:
                   desde 'proof', 'by', 'using' o 'apply' hasta el final.

Para cada pregunta se arma la teoría  contexto + enunciado + demostración,
y se le pregunta a Isabelle. Resultados posibles:

  aceptada       Isabelle la acepta y respeta el estilo pedido
  estilo         Isabelle la acepta, pero la pregunta pedía deducción
                 natural y la demostración usa métodos automáticos (auto,
                 simp, blast, metis, ...)
  rechazada      Isabelle no la acepta
  trampa         la respuesta intenta añadir axiomas, lemas o comandos
                 que no son parte de una demostración; no se verifica
  sin respuesta  el asistente no respondió esa pregunta

Uso:
    python3 evaluar.py benchmark.json respuestas.json [--paralelo 4] [--informe informe.json]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from concurrent.futures import ThreadPoolExecutor

from verificador import verificar, a_ascii

# Comandos que no pueden aparecer dentro de una demostración: con ellos se
# podría cambiar el enunciado, añadir axiomas o salirse de la prueba.
PROHIBIDOS = """lemma theorem corollary proposition schematic_goal axiomatization
axioms definition abbreviation fun function primrec datatype codatatype
consts declare setup local_setup method_setup attribute_setup oracle ML
ML_file ML_val ML_command ML_prf theory end notepad context locale
interpretation instantiation sorry oops""".split()

# Métodos automáticos: no valen cuando se pide deducción natural.
AUTOMATICOS = """auto simp simp_all blast fast fastforce force best bestsimp
slowsimp clarsimp clarify safe metis meson smt presburger linarith arith
argo iprover sledgehammer nitpick nunchaku eval code_simp normalization try
try0 algebra order""".split()


def sin_textos(prueba: str) -> str:
    """Quita cadenas, cartuchos y comentarios: solo queda la estructura."""
    t = re.sub(r'"(?:[^"\\]|\\.)*"', ' ', prueba)
    t = re.sub(r'\\<open>.*?\\<close>', ' ', t, flags=re.S)
    t = re.sub(r'\(\*.*?\*\)', ' ', t, flags=re.S)
    return t


def palabras(texto: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", texto))


def evaluar_una(pregunta: dict, prueba: str | None, tiempo_max: int) -> dict:
    r = {"id": pregunta["id"], "estilo_pedido": pregunta["estilo"]}
    if not prueba or not prueba.strip():
        return {**r, "resultado": "sin respuesta"}
    prueba = a_ascii(prueba)
    estructura = palabras(sin_textos(prueba))
    trampas = sorted(estructura & set(PROHIBIDOS))
    if trampas:
        return {**r, "resultado": "trampa", "detalle": "usa " + ", ".join(trampas)}
    teoria = pregunta["contexto"] + pregunta["enunciado"] + "\n" + prueba.strip() + "\n\nend\n"
    v = verificar(teoria, tiempo_max=tiempo_max)
    r["segundos"] = round(v.segundos, 1)
    if not v.ok:
        return {**r, "resultado": "rechazada",
                "detalle": "tiempo agotado" if v.agotado else "\n".join(v.errores)[:1500]}
    automaticos = sorted(estructura & set(AUTOMATICOS))
    if pregunta["estilo"] == "dn" and automaticos:
        return {**r, "resultado": "estilo", "detalle": "usa " + ", ".join(automaticos)}
    return {**r, "resultado": "aceptada"}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("benchmark")
    p.add_argument("respuestas")
    p.add_argument("--paralelo", type=int, default=2, help="verificaciones simultáneas")
    p.add_argument("--tiempo", type=int, default=60, help="segundos por demostración")
    p.add_argument("--informe", help="guardar el detalle en este archivo JSON")
    a = p.parse_args()

    with open(a.benchmark, encoding="utf-8") as f:
        preguntas = json.load(f)
    with open(a.respuestas, encoding="utf-8") as f:
        respuestas = json.load(f)

    with ThreadPoolExecutor(max_workers=a.paralelo) as ex:
        resultados = list(ex.map(
            lambda q: evaluar_una(q, respuestas.get(q["id"]), a.tiempo), preguntas))

    cuenta: dict[str, int] = {}
    for r in resultados:
        cuenta[r["resultado"]] = cuenta.get(r["resultado"], 0) + 1
        marca = {"aceptada": "OK ", "estilo": "EST", "rechazada": "NO ",
                 "trampa": "!! ", "sin respuesta": " - "}[r["resultado"]]
        linea = f"{marca} {r['id']}"
        if r.get("detalle") and r["resultado"] != "rechazada":
            linea += f"   ({r['detalle']})"
        print(linea)

    n = len(preguntas)
    verificadas = cuenta.get("aceptada", 0) + cuenta.get("estilo", 0)
    print("\nResumen")
    print(f"  preguntas                     {n}")
    print(f"  verificadas por Isabelle      {verificadas}  ({100*verificadas/n:.0f}%)")
    print(f"  aceptadas con el estilo pedido {cuenta.get('aceptada', 0)}  "
          f"({100*cuenta.get('aceptada', 0)/n:.0f}%)")
    for clave in ("estilo", "rechazada", "trampa", "sin respuesta"):
        if cuenta.get(clave):
            print(f"  {clave:<29} {cuenta[clave]}")
    if a.informe:
        with open(a.informe, "w", encoding="utf-8") as f:
            json.dump(resultados, f, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
