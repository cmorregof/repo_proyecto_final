# fragmentar.py  ---  partir el corpus en pedazos que se puedan citar
# Regla: por comandos, no por tamano. Un lema partido por la mitad no sirve.
import pathlib, re, shutil, subprocess

COMANDOS = re.compile(r"^(lemma|theorem|corollary|proposition|definition|fun|"
                      r"primrec|datatype|inductive|abbreviation|text|"
                      r"chapter|section|subsection|end)\b")
NOMBRE = re.compile(r"^\w+\s+(\w+)")


def fragmentar_thy(ruta, raiz):
    """Un fragmento = un comando con todo lo que le sigue hasta el proximo.
    Los bloques text que van justo antes de un lema se le pegan al lema:
    ahi suele estar el enunciado en palabras ("Ejercicio 3. Demostrar ...")."""
    lineas = pathlib.Path(ruta).read_text(encoding="utf-8").splitlines()
    fuente = str(pathlib.Path(ruta).relative_to(raiz))

    bloques, actual, inicio = [], [], 1          # 1) cortar en cada comando
    for i, linea in enumerate(lineas, 1):
        if COMANDOS.match(linea) and actual:
            bloques.append((inicio, actual))
            actual, inicio = [], i
        actual.append(linea)
    if actual:
        bloques.append((inicio, actual))

    frags, texto_previo = [], None                # 2) pegar text al lema
    for inicio, bl in bloques:
        m = re.match(r"\w+", bl[0])
        cmd = m.group(0) if m else ""
        if cmd == "text":                         # varios text seguidos se juntan
            texto_previo = (texto_previo[0], texto_previo[1] + bl) if texto_previo else (inicio, bl)
            continue
        if cmd in ("lemma", "theorem", "corollary", "proposition") and texto_previo:
            inicio, bl = texto_previo[0], texto_previo[1] + bl
            texto_previo = None
        elif texto_previo:
            frags.append(_frag(fuente, *texto_previo, tipo="texto"))
            texto_previo = None
        if cmd != "end":
            frags.append(_frag(fuente, inicio, bl, tipo=cmd))
    if texto_previo:
        frags.append(_frag(fuente, *texto_previo, tipo="texto"))
    return frags


def _frag(fuente, inicio, lineas, tipo):
    texto = "\n".join(lineas).strip()
    cabeza = next((l for l in lineas if not l.startswith("text")
                   and COMANDOS.match(l)), lineas[0])
    m = NOMBRE.match(cabeza)
    nombre = m.group(1).rstrip(":") if m and tipo not in ("texto", "section",
                                                          "subsection", "chapter") else ""
    # un lema que termina en oops o sorry no trae demostracion: es un enunciado
    sin_prueba = re.search(r"^\s*(oops|sorry)\s*$", texto, re.M) is not None
    return {"fuente": fuente, "linea": inicio, "tipo": tipo, "nombre": nombre,
            "con_prueba": tipo in ("lemma", "theorem", "corollary", "proposition")
                          and not sin_prueba,
            "texto": texto}


def paginas_pdf(ruta):
    """Texto de cada pagina. Usa pdftotext si existe; si no, pypdf."""
    if shutil.which("pdftotext"):
        salida = subprocess.run(["pdftotext", "-layout", str(ruta), "-"],
                                capture_output=True, text=True).stdout
        return salida.split("\f")                 # pdftotext separa paginas con \f
    try:
        from pypdf import PdfReader
    except ImportError:
        return None
    return [p.extract_text() or "" for p in PdfReader(str(ruta)).pages]


def bloques(texto, maximo=600):
    """Parte una pagina en bloques de a lo sumo ~maximo caracteres, cortando en
    lineas en blanco. Una pagina entera es larga y BM25 castiga lo largo."""
    partes = [p.strip() for p in re.split(r"\n\s*\n", texto) if p.strip()]
    salida, actual = [], ""
    for p in partes:
        if actual and len(actual) + len(p) > maximo:
            salida.append(actual)
            actual = ""
        actual = (actual + "\n\n" + p) if actual else p
    if actual:
        salida.append(actual)
    return salida


def fragmentar_pdf(ruta, raiz):
    """Bloques de cada pagina; se cita como documento y pagina."""
    paginas = paginas_pdf(ruta)
    if paginas is None:
        return None
    fuente = str(pathlib.Path(ruta).relative_to(raiz))
    frags = []
    for n, t in enumerate(paginas, 1):
        siguiente = set(paginas[n].split()) if n < len(paginas) else set()
        if t.split() and set(t.split()) <= siguiente:
            continue        # diapositiva con animacion: la pagina siguiente ya la contiene
        for b in bloques(t):
            if len(b) > 40:
                frags.append({"fuente": fuente, "pagina": n, "tipo": "pagina", "nombre": "",
                              "con_prueba": False, "texto": b})
    return frags
