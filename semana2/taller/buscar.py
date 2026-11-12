# buscar.py  ---  BM25: recuperacion por palabras, en Python puro
# Uso:  python3 buscar.py "conjE"
#       python3 buscar.py "regla de eliminacion de la disyuncion" 3
import json, math, os, re, sys
from collections import Counter
from normalizar import normalizar

AQUI = os.path.dirname(os.path.abspath(__file__))


def tokens(texto):
    """Palabras sueltas y pares de palabras seguidas. Los pares guardan algo de
    la estructura: 'p implies q' no es lo mismo que 'q implies p'."""
    t = re.findall(r"[a-z_][a-z0-9_']*|[0-9]+", normalizar(texto))
    return t + [a + "+" + b for a, b in zip(t, t[1:])]


class BM25:
    def __init__(self, frags, k1=1.5, b=0.75):
        self.frags, self.k1, self.b = frags, k1, b
        self.docs = [Counter(tokens(f["texto"])) for f in frags]
        self.long = [sum(d.values()) for d in self.docs]
        self.prom = sum(self.long) / len(self.long)
        N = len(self.docs)
        df = Counter(t for d in self.docs for t in d)
        self.idf = {t: math.log(1 + (N - n + 0.5) / (n + 0.5)) for t, n in df.items()}

    def puntaje(self, q, i):
        d, s = self.docs[i], 0.0
        for t in q:
            if t in d:
                tf = d[t]
                s += self.idf[t] * tf * (self.k1 + 1) / (
                    tf + self.k1 * (1 - self.b + self.b * self.long[i] / self.prom))
        return s

    def buscar(self, consulta, k=5, filtro=None):
        """Los k fragmentos con mayor puntaje. filtro: funcion frag -> bool."""
        q = tokens(consulta)
        puntajes = [(self.puntaje(q, i), i) for i in range(len(self.docs))
                    if filtro is None or filtro(self.frags[i])]
        puntajes.sort(reverse=True)
        return [dict(self.frags[i], puntaje=round(s, 2)) for s, i in puntajes[:k] if s > 0]


def cargar(archivo=os.path.join(AQUI, "indice.json")):
    if not os.path.exists(archivo):
        sys.exit("No encuentro indice.json: corran primero  python3 indexar.py")
    return BM25(json.load(open(archivo, encoding="utf-8")))


def donde(f):
    """Como se cita un fragmento: archivo y linea, o documento y pagina."""
    if "pagina" in f:
        return f"{f['fuente']}, pag. {f['pagina']}"
    return f"{f['fuente']}, linea {f['linea']}" + (f" ({f['nombre']})" if f["nombre"] else "")


if __name__ == "__main__":
    indice = cargar()
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    for f in indice.buscar(sys.argv[1], k):
        print(f"[{f['puntaje']:6.2f}] {donde(f)}")
        print("         " + f["texto"][:160].replace("\n", "\n         ") + "\n")
