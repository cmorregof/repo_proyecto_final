# Razonamiento Automático — Proyecto final

Asistente con recuperación (RAG) que propone demostraciones y se las hace
verificar a Isabelle. **El modelo propone; Isabelle decide.**

Curso del profesor Fabián Serrano · UNAL Manizales · asesorías de Carlos Orrego.

## Contenido

| Carpeta / archivo | Qué es |
|---|---|
| `ProyectoFinal.pdf` | El enunciado del proyecto. Léanlo primero. |
| `Recursos/` | El kit del profesor: `verificador.py`, `evaluar.py`, `benchmark_R1.json` y el `README.md` con instrucciones. |
| `taller_semana1/` | El código del taller del jueves 1: la configuración 1 (solo el modelo). |

## Antes de empezar

1. **Isabelle2025-2** funcionando (el del curso). Si `isabelle` no está en el PATH:
   `export ISABELLE=/Applications/Isabelle2025-2.app/bin/isabelle` (Mac) o
   `export ISABELLE=$HOME/Isabelle2025-2/bin/isabelle` (Linux).
2. **Python 3.9 o posterior.** No hay que instalar paquetes.
3. **Un modelo de lenguaje gratuito**, uno de estos dos caminos:
   - **Ollama** (recomendado, sin límite y sin internet): instálenlo desde
     [ollama.com](https://ollama.com) y descarguen el modelo:
     `ollama pull gemma3:4b` (unos 3 GB).
   - **OpenRouter** (si su computador no aguanta el modelo local): creen una
     llave gratuita y expórtenla: `export OPENROUTER_API_KEY=...`. Luego en
     `taller_semana1/modelo.py` cambien `"proveedor"` a `"openrouter"` y
     `"modelo"` a un modelo terminado en `:free`.
     **Nunca suban la llave al repositorio.**

## Cómo obtenerlo

```bash
git clone https://github.com/cmorregof/repo_proyecto_final.git
cd repo_proyecto_final
```

O con el botón verde **Code → Download ZIP**.

## Taller de la semana 1

```bash
cd taller_semana1
python3 paso1c.py              # ¿responde el modelo?
python3 config1.py 3           # configuración 1 con 3 preguntas
python3 ../Recursos/evaluar.py ../Recursos/benchmark_R1.json respuestas_config1.json \
        --paralelo 4 --informe informe_c1.json
```

Cuando funcione con 3, corran las 58: `python3 config1.py`. Ese resultado es
su **línea base**.

## Tarea para el próximo jueves

1. Configuración 1 completa sobre las 58: respuestas, registro (`registros/`) e informe.
2. Leer diez registros y clasificar los errores del modelo.
3. Tema de formalización (tres opciones en orden) y dos enunciados en Isabelle.
