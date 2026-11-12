# Razonamiento Automático — Proyecto final

**Asistente con recuperación (RAG) que propone demostraciones y se las hace verificar a Isabelle.**
Curso del profesor Fabián Serrano · Universidad Nacional de Colombia, Sede Manizales, 2026-II · Asesorías: Carlos Orrego.

> **El modelo propone; Isabelle decide.**
> Todo el proyecto se puede hacer gratis: el modelo corre en su propio computador (Ollama + Gemma 3) y el código usa solo la biblioteca estándar de Python.

## Empezar aquí

1. Leer el [enunciado del proyecto (PDF)](ProyectoFinal.pdf).
2. Leer el [Manual de la semana 1 (PDF)](semana1/Manual_Semana1.pdf): instalación, el kit del profesor y el taller paso a paso.
3. Clonar el repositorio y correr el taller:

```bash
git clone https://github.com/cmorregof/repo_proyecto_final.git
cd repo_proyecto_final/semana1/taller
python3 paso1c.py          # ¿responde el modelo?
python3 config1.py 3       # configuración 1 con 3 preguntas
```

Si ya lo habían clonado: `git pull`.

**Semana 2:** `cd semana2/taller && python3 indexar.py && python3 medir_recuperacion.py`, luego `python3 config2.py 3`. El corpus del curso está en [`ConjuntoDatos/`](ConjuntoDatos), con autorización del profesor Fabián.

## Materiales semana a semana

| Jueves | Tema | Manual | Diapositivas | Código |
|---|---|---|---|---|
| 1 · 5 nov | **El hilo:** el modelo y la línea base (configuración 1) | [Manual (PDF)](semana1/Manual_Semana1.pdf) | [Diapositivas (PDF)](semana1/Diapositivas_Semana1.pdf) | [`semana1/taller/`](semana1/taller) |
| 2 · 12 nov | **La biblioteca:** buscar en los documentos y citar (configuración 2) | [Manual (PDF)](semana2/Manual_Semana2.pdf) | [Diapositivas (PDF)](semana2/Diapositivas_Semana2.pdf) | [`semana2/taller/`](semana2/taller) |
| 3 | **La flecha roja:** verificar con Isabelle y corregir (configuración 3) | — | — | — |
| 4 | **El espejo:** evaluar, analizar errores, informe | — | — | — |

Los materiales de cada jueves se publican ese día.

## Modelos

| Camino | Qué es | Cuándo |
|---|---|---|
| **A · Ollama** (recomendado) | Gemma 3 4B en su propio computador: `ollama pull gemma3:4b`, luego `ollama serve` en una terminal aparte | Sin límite, sin llave, sin internet. 8 GB de RAM. |
| **B · OpenRouter** | Modelos `:free` por internet, con llave en la variable `OPENROUTER_API_KEY` | Si su computador no aguanta el modelo local. Límite diario. |

Se cambia de modelo en `CONFIG` (`semana1/taller/modelo.py`). **Regla:** las tres configuraciones del informe, con el mismo modelo. **Nunca suban una llave al repositorio.**

## El kit del profesor

La carpeta [`Recursos/`](Recursos) trae `verificador.py` (preguntarle a Isabelle), `evaluar.py` (la calificación, la misma que usará el profesor), `benchmark_R1.json` (las 58 preguntas públicas) y su propio [README](Recursos/README.md). Si `isabelle` no está en el PATH:

```bash
export ISABELLE=/Applications/Isabelle2025-2.app/bin/isabelle   # Mac (ajusten la versión)
export ISABELLE=$HOME/Isabelle2025-2/bin/isabelle               # Linux
```

## Honestidad

Se califica la **mejora** sobre la línea base del mismo modelo, no el porcentaje absoluto. Un asistente que resuelve el 30 % y nunca miente sobre el veredicto vale más que uno que resuelve el 60 % y a veces presenta pruebas sin verificar. El uso de IA para programar está permitido: declárenlo en el informe.

## Estructura del repositorio

```
ProyectoFinal.pdf   Enunciado del proyecto (prof. Fabián Serrano)
Recursos/           Kit del profesor: verificador, evaluador, benchmark público
semana1/            Manual, diapositivas y taller de la configuración 1
  taller/           modelo.py, utilidades.py, prompt.py, config1.py, paso1c.py
semana2/ …          Se agregan cada jueves
```
