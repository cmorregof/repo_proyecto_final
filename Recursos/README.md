# Kit del proyecto final

Herramientas para conectar su asistente con Isabelle y para evaluarlo. Lea
primero el enunciado, `../ProyectoFinal.pdf`.

| Archivo | Para qué |
|---|---|
| `verificador.py` | Le pregunta a Isabelle si un texto de teoría es correcto. Es la pieza que su asistente debe llamar antes de mostrar cualquier demostración. |
| `benchmark_R1.json` | Benchmark público: los 58 ejercicios de la relación 1, estilo deducción natural. |
| `evaluar.py` | Califica un archivo de respuestas contra un benchmark. Es lo mismo que usará el profesor. |
| `construir_benchmark.py` | Convierte una relación de ejercicios `.thy` en un benchmark. Úselo con la formalización de su equipo. |
| `comparar_enunciados.py` | Comprueba que su archivo de enunciados y el de soluciones enuncian lo mismo. |
| `ejemplo_respuestas.json` | El formato del archivo de respuestas, con dos ejemplos. |

Solo usan la biblioteca estándar de Python (3.9 o posterior).

## 1. Indicar dónde está Isabelle

Si `isabelle` no está en el PATH:

```bash
export ISABELLE=/Applications/Isabelle2025-2.app/bin/isabelle
```

En Linux, la ruta suele ser `$HOME/Isabelle2025-2/bin/isabelle`.

## 2. Verificar desde Python

```python
from verificador import verificar

r = verificar('lemma "p ∧ q ⟹ q ∧ p" by auto')
print(r.ok, r.segundos)
for e in r.errores:
    print(e)
```

- Acepta una teoría completa o solo su cuerpo; en ese caso la envuelve en
  una teoría que importa `Main`.
- **Convierte los símbolos** `∧ ⟶ ∀ ⟦ ⟧ ‹ ›` a la forma `\<and>` que exige
  Isabelle. Los modelos de lenguaje escriben Unicode, y un solo símbolo
  crudo en un archivo `.thy` produce *Inner lexical error*.
- Los errores vienen limpios, con la línea **del texto que usted envió**.
  Devuélvaselos al modelo para que corrija.
- `tiempo_max` (segundos, por defecto 120) corta las pruebas que no
  terminan, como un `apply (rule ccontr)+`.
- `sorry` no pasa: Isabelle lo rechaza por sí mismo.

Cada verificación tarda unos 4 o 5 segundos, casi todo en arrancar
Isabelle. Si eso les pesa, `isabelle server` mantiene Isabelle abierto
entre verificaciones; usarlo es una mejora opcional.

## 3. Evaluar su asistente

Su asistente debe producir un archivo de respuestas: para cada `id` del
benchmark, la demostración que va **después** del enunciado (desde
`proof`, `by`, `using` o `apply`). Vea `ejemplo_respuestas.json`.

```bash
python3 evaluar.py benchmark_R1.json respuestas.json --paralelo 4 --informe informe.json
```

Cada pregunta termina en uno de estos estados:

| Estado | Significa |
|---|---|
| `aceptada` | Isabelle la acepta y respeta el estilo pedido |
| `estilo` | Isabelle la acepta, pero se pedía deducción natural y usa `auto`, `simp`, `blast`, `metis`... |
| `rechazada` | Isabelle no la acepta; el informe trae el error |
| `trampa` | Intenta añadir lemas, axiomas, `sorry` u otros comandos; ni se verifica |
| `sin respuesta` | No hay respuesta para esa pregunta |

Con el ejemplo, la primera sale `aceptada` y la segunda `estilo`.

Con 4 verificaciones en paralelo, las 58 preguntas de R1 tardan unos dos
minutos.

> **Ojo con el benchmark público.** Las soluciones de R1 están en el libro
> de Alonso de 2018, que es parte del corpus. Un buen resultado aquí mide
> sobre todo que su recuperación funciona. El benchmark privado, con
> ejercicios cuyas soluciones no están en el corpus, mide lo demás.

## 4. Para la formalización de su equipo

Escriba dos archivos con los mismos nombres de lema, `ejercicio_...`:
uno de enunciados terminados en `oops` y otro con las soluciones.

```bash
python3 comparar_enunciados.py mis_enunciados.thy mis_soluciones.thy
python3 construir_benchmark.py mis_soluciones.thy --relacion EQ3 --estilo libre > bench_EQ3.json
```

Si se construye desde el archivo de **soluciones**, cada ejercicio puede
usar los anteriores ya demostrados.
