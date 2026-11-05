# paso1c.py  ---  primera conversacion con el modelo
from modelo import preguntar

respuesta = preguntar([
    {"role": "system", "content": "Eres un experto en Isabelle/Isar."},
    {"role": "user",   "content": "Que dice la regla mp?"},
])
print(respuesta)
