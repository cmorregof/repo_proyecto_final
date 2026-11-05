#!/usr/bin/env python3
"""Comprueba que una relacion de enunciados y su archivo de soluciones
enuncian lo mismo.

Compara, lema por lema, todos los 'lemma/theorem ejercicio_*': mismo
nombre, mismos atributos y mismo enunciado (assumes/shows incluidos),
ignorando espacios. Informa de los que faltan en uno u otro archivo y de
los que difieren. Un 'undefined' puesto a proposito en el enunciado (para
que el estudiante lo complete) aparece como diferencia: hay que mirarlo.

Uso:  python3 comparar_enunciados.py enunciados.thy soluciones.thy
"""
import re
import sys


def sin_comentarios(texto):
    """Quita los (* ... *), respetando que en Isabelle se anidan."""
    salida, nivel, i = [], 0, 0
    while i < len(texto):
        if texto.startswith('(*', i):
            nivel, i = nivel + 1, i + 2
        elif texto.startswith('*)', i) and nivel:
            nivel, i = nivel - 1, i + 2
        else:
            if not nivel:
                salida.append(texto[i])
            i += 1
    return ''.join(salida)


RE_LEMA = re.compile(
    r'(?:lemma|theorem)\s+(ejercicio_\w+)(\s*\[[^\]]*\])?\s*:?(.*?)'
    r'(?=\n\s*(?:oops|by|proof|apply|using)\b)', re.S)


def enunciados(ruta):
    texto = sin_comentarios(open(ruta, encoding='utf-8').read())
    return {m.group(1): ' '.join(((m.group(2) or '') + ' ' + m.group(3)).split())
            for m in RE_LEMA.finditer(texto)}


def main(enun, sol):
    e, s = enunciados(enun), enunciados(sol)
    print(f'enunciados: {len(e)}   soluciones: {len(s)}')
    problemas = 0
    for k in sorted(set(e) | set(s)):
        if k not in s:
            print('  FALTA SOLUCION ', k); problemas += 1
        elif k not in e:
            print('  FALTA ENUNCIADO', k); problemas += 1
        elif e[k] != s[k]:
            print('  DIFIERE', k, '\n     enunciado:', e[k], '\n     solucion: ', s[k])
            problemas += 1
    return 1 if problemas else 0


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(__doc__); sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2]))
