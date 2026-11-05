# modelo.py  ---  hablar con un modelo de lenguaje (solo biblioteca estandar)
import json, os, urllib.request

CONFIG = {
    "proveedor":   "ollama",      # o "openrouter"
    "modelo":      "gemma3:4b",   # o el nombre de otro modelo
    "temperatura": 0.2,           # baja = respuestas mas estables
}

URLS = {
    "ollama":     "http://localhost:11434/v1/chat/completions",
    "openrouter": "https://openrouter.ai/api/v1/chat/completions",
}


def preguntar(mensajes, cfg=CONFIG):
    """Entra una lista de mensajes; sale el texto de la respuesta."""
    cabeceras = {"Content-Type": "application/json"}
    if cfg["proveedor"] == "openrouter":                       # solo aqui hay llave
        cabeceras["Authorization"] = "Bearer " + os.environ["OPENROUTER_API_KEY"]

    cuerpo = json.dumps({"model": cfg["modelo"],
                         "messages": mensajes,
                         "temperature": cfg["temperatura"]}).encode("utf-8")

    req = urllib.request.Request(URLS[cfg["proveedor"]], data=cuerpo, headers=cabeceras)
    with urllib.request.urlopen(req, timeout=300) as r:
        return json.load(r)["choices"][0]["message"]["content"]
