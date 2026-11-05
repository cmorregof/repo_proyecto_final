#!/usr/bin/env python3
"""Construye un benchmark a partir de una relación de ejercicios (.thy).

Cada lema llamado 'ejercicio_...' se convierte en una pregunta del
benchmark, con:
  - id:        relación/nombre del lema
  - estilo:    'dn' (solo reglas de deducción natural) o 'libre'
  - enunciado: el lema tal como está escrito, sin la demostración
  - contexto:  todo lo que hay antes en el archivo (definiciones, lemas
               previos); el asistente lo necesita para entender el
               enunciado, y el evaluador lo antepone al verificar.

Si el archivo trae soluciones, el contexto incluye las de los ejercicios
anteriores, que así pueden usarse en los siguientes.

Uso:
    python3 construir_benchmark.py R1_Deduccion_natural_enunciados.thy \\
        --relacion R1 --estilo dn  > benchmark_R1.json
"""
from __future__ import annotations

import argparse
import json
import re
import sys

RE_LEMA = re.compile(
    r'^(?:lemma|theorem)\s+(ejercicio_\w+)\b.*?'
    r'(?=\n\s*(?:oops|by|proof|apply|using)\b)', re.S | re.M)


def construir(texto: str, relacion: str, estilo: str) -> list[dict]:
    preguntas = []
    for m in RE_LEMA.finditer(texto):
        preguntas.append({
            "id": f"{relacion}/{m.group(1)}",
            "estilo": estilo,
            # un 'using ...' al final del enunciado ya es parte de la prueba
            "enunciado": re.sub(r'\s+using\s+[^\n"]*$', '', m.group(0).rstrip()),
            "contexto": texto[:m.start()],
        })
    return preguntas


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("archivo")
    p.add_argument("--relacion", required=True, help="prefijo de los id, p. ej. R1")
    p.add_argument("--estilo", choices=["dn", "libre"], default="libre")
    a = p.parse_args()
    with open(a.archivo, encoding="utf-8") as f:
        preguntas = construir(f.read(), a.relacion, a.estilo)
    json.dump(preguntas, sys.stdout, ensure_ascii=False, indent=1)
    print(f"{len(preguntas)} preguntas", file=sys.stderr)


if __name__ == "__main__":
    main()
