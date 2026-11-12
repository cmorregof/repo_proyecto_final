# indexar.py  ---  recorrer el corpus y guardar los fragmentos en indice.json
# Uso:  python3 indexar.py                 (corpus: ../../ConjuntoDatos)
#       python3 indexar.py otra/carpeta    (por ejemplo, con su formalizacion)
import collections, json, os, pathlib, sys
from fragmentar import fragmentar_thy, fragmentar_pdf

AQUI = pathlib.Path(__file__).resolve().parent
RAIZ = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else AQUI.parent.parent / "ConjuntoDatos"

frags, sin_pdf = [], []
for ruta in sorted(RAIZ.rglob("*")):
    if ruta.suffix == ".thy":
        frags += fragmentar_thy(ruta, RAIZ)
    elif ruta.suffix == ".pdf":
        nuevos = fragmentar_pdf(ruta, RAIZ)
        if nuevos is None:
            sin_pdf.append(ruta.name)
        else:
            frags += nuevos

json.dump(frags, open(AQUI / "indice.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=0)

por_tipo = collections.Counter(f["tipo"] for f in frags)
print(f"{len(frags)} fragmentos de {RAIZ}")
for tipo, n in por_tipo.most_common():
    print(f"  {tipo:<12} {n}")
print(f"  lemas con demostracion: {sum(f['con_prueba'] for f in frags)}")
if sin_pdf:
    print(f"\nOJO: {len(sin_pdf)} PDF sin indexar (no hay pdftotext ni pypdf).")
    print("  Instalen uno:  pip install pypdf   o   brew install poppler")
print("Listo: indice.json")
