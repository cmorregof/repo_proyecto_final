#!/usr/bin/env python3
"""Verificador: le pregunta a Isabelle si un texto de teoría es correcto.

Es la pieza central del proyecto. El modelo de lenguaje propone; Isabelle
decide. Ninguna demostración se le muestra al usuario como correcta si no
pasó por aquí.

Uso como biblioteca:

    from verificador import verificar
    r = verificar('''
    theory Prueba imports Main begin
    lemma "p \\<and> q \\<Longrightarrow> q \\<and> p" by auto
    end
    ''')
    r.ok         # True si Isabelle la acepta
    r.errores    # los mensajes de error de Isabelle, si los hay
    r.segundos   # cuánto tardó

Uso desde la terminal:

    python3 verificador.py archivo.thy

Requiere Isabelle2025-2 instalado. Si el ejecutable no está en el PATH,
indique su ruta en la variable de entorno ISABELLE, por ejemplo
    export ISABELLE=/Applications/Isabelle2025-2.app/bin/isabelle      (macOS)
    export ISABELLE=$HOME/Isabelle2025-2/bin/isabelle                  (Linux)

Cómo funciona: escribe la teoría en un directorio temporal junto con un
archivo ROOT que declara una sesión sobre HOL, ejecuta `isabelle build`, y
lee los mensajes que empiezan por '***'. Cada verificación usa una sesión
de nombre único, de modo que se pueden lanzar varias en paralelo, y al
terminar borra los registros que Isabelle guarda de esa sesión.
"""
from __future__ import annotations

import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass, field
from functools import lru_cache

ISABELLE = os.environ.get("ISABELLE", "isabelle")


@dataclass
class Resultado:
    ok: bool
    errores: list[str] = field(default_factory=list)
    segundos: float = 0.0
    agotado: bool = False          # True si se acabó el tiempo

    def __str__(self) -> str:
        if self.ok:
            return f"Correcta ({self.segundos:.1f} s)"
        motivo = "tiempo agotado" if self.agotado else "rechazada"
        return f"{motivo.capitalize()} ({self.segundos:.1f} s)\n" + "\n".join(self.errores)


# --------------------------------------------------------------------------
# Símbolos: los modelos de lenguaje escriben ∧, ⟶, ∀ ... pero en un archivo
# de teoría Isabelle exige la forma ASCII \<and>, \<longrightarrow>, \<forall>.
# Un solo símbolo crudo produce "Inner lexical error".
# --------------------------------------------------------------------------

def _getenv(variable: str) -> str:
    salida = subprocess.run([ISABELLE, "getenv", "-b", variable],
                            capture_output=True, text=True, check=True)
    return salida.stdout.strip()


@lru_cache(maxsize=1)
def tabla_simbolos() -> dict[str, str]:
    """Carácter Unicode -> nombre ASCII de Isabelle, según etc/symbols."""
    ruta = os.path.join(_getenv("ISABELLE_HOME"), "etc", "symbols")
    tabla: dict[str, str] = {}
    with open(ruta, encoding="utf-8") as f:
        for linea in f:
            m = re.match(r"(\\<[^>]+>)\s+code:\s*(0x[0-9a-fA-F]+)", linea.strip())
            if m:
                tabla.setdefault(chr(int(m.group(2), 16)), m.group(1))
    return tabla


def a_ascii(texto: str) -> str:
    """Convierte cada símbolo Unicode de Isabelle a su forma \\<nombre>.

    Los acentos y la ñ no se tocan: no son símbolos de Isabelle.
    """
    tabla = tabla_simbolos()
    return "".join(tabla.get(c, c) for c in texto)


# --------------------------------------------------------------------------
# Verificación
# --------------------------------------------------------------------------

def _nombre_teoria(texto: str) -> str | None:
    m = re.search(r"^\s*theory\s+([A-Za-z][A-Za-z0-9_']*)", texto, re.M)
    return m.group(1) if m else None


def _errores(salida: str) -> list[str]:
    """Agrupa las líneas '*** ...' de la salida en mensajes."""
    mensajes, actual = [], []
    for linea in salida.splitlines():
        if linea.startswith("***"):
            contenido = linea[3:].strip()
            if contenido:
                actual.append(contenido)
            elif actual:
                mensajes.append("\n".join(actual)); actual = []
        elif actual:
            mensajes.append("\n".join(actual)); actual = []
    if actual:
        mensajes.append("\n".join(actual))
    # quitar el ruido final de build ("The error(s) above occurred ...")
    utiles = [m for m in mensajes
              if not m.startswith("The error(s) above occurred")
              and not m.startswith("Unfinished session")]
    return utiles or mensajes


def _limpiar_rutas(mensaje: str, desfase: int) -> str:
    """'(line 7 of "/tmp/.../X.thy")' -> '(línea 3)', en líneas del texto original."""
    def cambio(m: re.Match) -> str:
        return f"(línea {max(1, int(m.group(1)) - desfase)})"
    return re.sub(r'\(line (\d+) of "[^"]*"\)', cambio, mensaje)


def _borrar_registros(sesion: str) -> None:
    try:
        heaps = _getenv("ISABELLE_HEAPS")
    except Exception:
        return
    for ruta in glob.glob(os.path.join(heaps, "*", "log", sesion + "*")):
        try:
            os.remove(ruta)
        except OSError:
            pass


def verificar(teoria: str, tiempo_max: int = 120, convertir_simbolos: bool = True) -> Resultado:
    """Compila `teoria` con Isabelle y devuelve el veredicto.

    `teoria` puede ser una teoría completa (theory X imports ... begin ...
    end) o solo su cuerpo; en ese caso se envuelve en una teoría que
    importa Main.
    """
    if convertir_simbolos:
        teoria = a_ascii(teoria)
    nombre = _nombre_teoria(teoria)
    desfase = 0
    if nombre is None:                     # solo el cuerpo: se envuelve
        nombre = "Verificacion"
        teoria = f"theory {nombre}\n  imports Main\nbegin\n\n{teoria}\n\nend\n"
        desfase = 4

    sesion = "V_" + uuid.uuid4().hex[:12]
    directorio = tempfile.mkdtemp(prefix="verificador_")
    inicio = time.time()
    try:
        with open(os.path.join(directorio, nombre + ".thy"), "w", encoding="utf-8") as f:
            f.write(teoria)
        with open(os.path.join(directorio, "ROOT"), "w", encoding="utf-8") as f:
            f.write(f'session {sesion} = HOL +\n'
                    f'  options [timeout = {tiempo_max}]\n'
                    f'  theories\n    {nombre}\n')
        try:
            proceso = subprocess.run([ISABELLE, "build", "-d", directorio, sesion],
                                     capture_output=True, text=True,
                                     timeout=tiempo_max + 60)
        except subprocess.TimeoutExpired:
            return Resultado(False, ["Tiempo agotado"], time.time() - inicio, agotado=True)
        salida = proceso.stdout + proceso.stderr
        segundos = time.time() - inicio
        if proceso.returncode == 0:
            return Resultado(True, [], segundos)
        agotado = "Timeout" in salida or "timeout" in salida
        errores = [_limpiar_rutas(e, desfase) for e in _errores(salida)]
        return Resultado(False, errores or [salida.strip()[-2000:]],
                         segundos, agotado=agotado)
    finally:
        shutil.rmtree(directorio, ignore_errors=True)
        _borrar_registros(sesion)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    with open(sys.argv[1], encoding="utf-8") as f:
        resultado = verificar(f.read())
    print(resultado)
    sys.exit(0 if resultado.ok else 1)
