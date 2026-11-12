 (* Programación funcional y razonamiento sobre programas --- ejercicios.
   Basados en las teorías vistas en clase:
     EjemplosTipoListas, EjemplosTipoNumerosNaturales y
     OtrosEjemplosListas.
   Dificultad: [*] básico, [**] medio, [***] avanzado. *)

theory Ejercicios_programacion_funcional
  imports Main
begin

chapter \<open>Programación funcional y razonamiento sobre programas --- ejercicios\<close>

text \<open>
  Instrucciones:
  \<^item> Sustituya cada \<open>oops\<close> por una demostración.
  \<^item> Antes de demostrar, pruebe el enunciado con \<open>value\<close> en algunos
    casos, o con \<open>quickcheck\<close>.
  \<^item> Donde se pida demostración detallada, escriba la cadena de
    igualdades con \<open>also\<close> y \<open>finally\<close>, como en clase.
  \<^item> Puede usar, en cualquier ejercicio, los lemas de ejercicios
    anteriores.
\<close>

section \<open>Definiciones vistas en clase\<close>

text \<open>Son las mismas de las teorías de clase. No las modifique.\<close>

fun inversa :: "'a list \<Rightarrow> 'a list" where
  "inversa [] = []"
| "inversa (x#xs) = inversa xs @ [x]"

fun conc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "conc [] ys = ys"
| "conc (x#xs) ys = x # (conc xs ys)"

fun longitud :: "'a list \<Rightarrow> nat" where
  "longitud [] = 0"
| "longitud (x#xs) = 1 + longitud xs"

fun par_nesimo :: "nat \<Rightarrow> nat" where
  "par_nesimo 0 = 0"
| "par_nesimo (Suc n) = 2*(n+1)"

fun Suma_pares :: "nat \<Rightarrow> nat" where
  "Suma_pares 0 = 0"
| "Suma_pares (Suc n) = (Suma_pares n) + 2*(n+1)"

fun Suma_impares :: "nat \<Rightarrow> nat" where
  "Suma_impares 0 = 0"
| "Suma_impares (Suc n) = (Suma_impares n) + 2*n+1"

fun Suma_naturales :: "nat \<Rightarrow> nat" where
  "Suma_naturales 0 = 0"
| "Suma_naturales (Suc n) = (Suma_naturales n) + n+1"

text \<open>Los tres lemas demostrados en clase, para poder usarlos:\<close>

lemma suma_pares: "Suma_pares n = n*(n+1)"
  by (induct n) auto

lemma suma_impares: "Suma_impares n = n*n"
  by (induct n) auto

lemma suma_naturales: "2*(Suma_naturales n) = n*(n+1)"
  by (induct n) auto

definition par :: "nat \<Rightarrow> bool" where
  "par n \<equiv> \<exists>m. n = m+m"

fun par1 :: "nat \<Rightarrow> bool" where
  "par1 0 = True"
| "par1 (Suc 0) = False"
| "par1 (Suc (Suc n)) = par1 n"

primrec repite :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "repite 0 x = []"
| "repite (Suc n) x = x # (repite n x)"

fun coge :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "coge n [] = []"
| "coge 0 xs = []"
| "coge (Suc n) (x#xs) = x # (coge n xs)"

fun elimina :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "elimina n [] = []"
| "elimina 0 xs = xs"
| "elimina (Suc n) (x#xs) = elimina n xs"

fun elimina1 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  elimina1_Nil:  "elimina1 n [] = []"
| elimina1_Cons: "elimina1 n (x#xs) = (case n of
                                         0 \<Rightarrow> x#xs
                                       | Suc m \<Rightarrow> drop m xs)"

fun todos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "todos p [] = True"
| "todos p (y#ys) = ((p y) \<and> (todos p ys))"


section \<open>Parte A --- Listas (EjemplosTipoListas)\<close>

text \<open>
  Ejercicio A1 [*]. Demostración detallada, como la de
  \<open>inversa [x] = [x]\<close> en clase: cada paso con \<open>simp only:\<close> y el
  nombre de la ecuación que usa (\<open>inversa.simps(1)\<close>,
  \<open>inversa.simps(2)\<close>, \<open>append_Nil\<close>, \<open>append_Cons\<close>).
\<close>
lemma ejercicio_A1: "inversa [x, y] = [y, x]"
  oops

text \<open>
  Ejercicio A2 [*]. La concatenación \<open>conc\<close> que definimos en clase
  coincide con la de la librería, \<open>@\<close>.
\<close>
lemma ejercicio_A2: "conc xs ys = xs @ ys"
  oops

text \<open>
  Ejercicio A3 [**]. Invertir una lista no cambia su longitud.
  Primero demuestre el lema auxiliar A3a.
\<close>
lemma ejercicio_A3a: "longitud (xs @ ys) = longitud xs + longitud ys"
  oops

lemma ejercicio_A3: "longitud (inversa xs) = longitud xs"
  oops

text \<open>
  Ejercicios A4 y A5 [**]. Los dos que quedaron planteados en clase.
  A5 sale fácil cuando A4 está demostrado y declarado \<open>[simp]\<close>.
\<close>
lemma ejercicio_A4 [simp]: "inversa (xs @ ys) = (inversa ys) @ (inversa xs)"
  oops

theorem ejercicio_A5 [simp]: "inversa (inversa xs) = xs"
  oops

text \<open>
  Ejercicio A6 [**]. Defina la función \<open>duplica\<close>, que repite cada
  elemento de una lista; por ejemplo
    \<open>duplica [1,2,3] = [1,1,2,2,3,3]\<close>.
  Sustituya la declaración \<open>consts\<close> por su definición con \<open>fun\<close>,
  pruébela con \<open>value\<close> y luego demuestre el lema.
\<close>
consts duplica :: "'a list \<Rightarrow> 'a list"

lemma ejercicio_A6: "longitud (duplica xs) = 2 * longitud xs"
  oops

text \<open>
  Ejercicio A7 [***]. \<questiondown>Es cierto que \<open>conc xs (inversa xs)\<close> y
  \<open>conc (inversa xs) xs\<close> son iguales? Compruébelo con \<open>quickcheck\<close>.
\<close>
lemma "conc xs (inversa xs) = conc (inversa xs) xs"
  oops

text \<open>
  Lo que sí es cierto: \<open>conc xs (inversa xs)\<close> es un palíndromo, se lee
  igual al derecho y al revés. Sugerencia: A2, A4 y A5.
\<close>
lemma ejercicio_A7: "inversa (conc xs (inversa xs)) = conc xs (inversa xs)"
  oops

text \<open>
  Ejercicio A8 [***]. \<open>inversa\<close> hace un \<open>@\<close> por elemento. Esta versión
  con acumulador es lineal: va pasando los elementos a \<open>ys\<close>.
\<close>
fun inversa_ac :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inversa_ac [] ys = ys"
| "inversa_ac (x#xs) ys = inversa_ac xs (x#ys)"

text \<open>
  Demuestre que calcula lo mismo que \<open>inversa\<close>. La inducción directa
  sobre A8 se atasca: demuestre antes el enunciado general A8a.
  Sugerencia: \<open>induct xs arbitrary: ys\<close>.
\<close>
lemma ejercicio_A8a: "inversa_ac xs ys = inversa xs @ ys"
  oops

lemma ejercicio_A8: "inversa_ac xs [] = inversa xs"
  oops


section \<open>Parte B --- Números naturales (EjemplosTipoNumerosNaturales)\<close>

text \<open>
  Ejercicio B1 [*]. \<questiondown>Qué calcula \<open>par_nesimo\<close>? Demuéstrelo.
  Pregunta: \<questiondown>hace falta inducción, o basta distinguir casos
  (\<open>cases n\<close>)?
\<close>
lemma ejercicio_B1: "par_nesimo n = 2 * n"
  oops

text \<open>
  Ejercicio B2 [*]. La suma de los \<open>n\<close> primeros pares es el doble de la
  de los \<open>n\<close> primeros naturales. Hágalo sin inducción, con los lemas de
  clase.
\<close>
lemma ejercicio_B2: "Suma_pares n = 2 * Suma_naturales n"
  oops

text \<open>
  Ejercicio B3 [**]. \<open>Suma_pot2 n\<close> es \<open>1 + 2 + 4 + ... + 2^(n-1)\<close>.
\<close>
fun Suma_pot2 :: "nat \<Rightarrow> nat" where
  "Suma_pot2 0 = 0"
| "Suma_pot2 (Suc n) = Suma_pot2 n + 2^n"

lemma ejercicio_B3: "Suma_pot2 n + 1 = 2^n"
  oops

text \<open>
  Ejercicio B4 [***]. La suma de los cubos es el cuadrado de la suma:
    \<open>1\<^sup>3 + 2\<^sup>3 + ... + n\<^sup>3 = (1 + 2 + ... + n)\<^sup>2\<close>.
  B4a por inducción, con demostración detallada. Para la cuenta del
  paso inductivo: \<open>simp add: power2_eq_square power3_eq_cube
  algebra_simps\<close>. B4b sale de B4a y de \<open>suma_naturales\<close>, sin
  inducción.
\<close>
fun Suma_cubos :: "nat \<Rightarrow> nat" where
  "Suma_cubos 0 = 0"
| "Suma_cubos (Suc n) = Suma_cubos n + (n+1)^3"

lemma ejercicio_B4a: "4 * Suma_cubos n = (n*(n+1))^2"
  oops

lemma ejercicio_B4b: "Suma_cubos n = (Suma_naturales n)^2"
  oops

text \<open>
  Ejercicio B5 [**]. En clase se demostró por inducción que la suma de
  dos pares es par. Demuéstrelo ahora sin inducción: obtenga los
  testigos con \<open>obtain\<close> y construya el nuevo con \<open>exI\<close>.
\<close>
lemma ejercicio_B5:
  assumes "par n" and "par m"
  shows "par (n+m)"
  oops

text \<open>Ejercicio B6 [**]. Un par por cualquier natural es par.\<close>
lemma ejercicio_B6:
  assumes "par n"
  shows "par (n*m)"
  oops

text \<open>Ejercicio B7 [**]. Con esta definición de impar:\<close>
definition impar :: "nat \<Rightarrow> bool" where
  "impar n \<equiv> \<exists>m. n = 2*m+1"

lemma ejercicio_B7a:
  assumes "par n"
  shows "impar (Suc n)"
  oops

lemma ejercicio_B7b:
  assumes "impar n"
  shows "par (Suc n)"
  oops

text \<open>
  Ejercicio B8 [***]. En clase se dijo que \<open>par1\<close> no es apropiada para
  demostrar. Pero sí se puede demostrar que coincide con \<open>par\<close>.
  Primero los tres lemas B8a, B8b, B8c (sugerencia: \<open>presburger\<close>
  después de \<open>simp add: par_def\<close>). Luego B8 por la inducción de la
  propia función: \<open>induct n rule: par1.induct\<close>.
\<close>
lemma ejercicio_B8a: "par 0"
  oops

lemma ejercicio_B8b: "\<not> par (Suc 0)"
  oops

lemma ejercicio_B8c: "par (Suc (Suc n)) = par n"
  oops

lemma ejercicio_B8: "par1 n = par n"
  oops


section \<open>Parte C --- Más listas (OtrosEjemplosListas)\<close>

text \<open>Ejercicio C1 [*]. \<open>todos\<close> y la concatenación.\<close>
lemma ejercicio_C1: "todos p (conc xs ys) = (todos p xs \<and> todos p ys)"
  oops

text \<open>Ejercicio C2 [*]. Todos los elementos de \<open>repite n x\<close> son \<open>x\<close>.\<close>
lemma ejercicio_C2: "todos (\<lambda>y. y = x) (repite n x)"
  oops

text \<open>
  Ejercicio C3 [**]. Repetir \<open>m+n\<close> veces es repetir \<open>m\<close> y luego \<open>n\<close>.
  \<questiondown>Sobre cuál variable conviene la inducción?
\<close>
lemma ejercicio_C3: "repite (m + n) x = conc (repite m x) (repite n x)"
  oops

text \<open>
  Ejercicios C4 y C5 [**]. Longitudes. Use la inducción de la función:
  \<open>induct n xs rule: elimina.induct\<close> y \<open>coge.induct\<close>.
\<close>
lemma ejercicio_C4: "longitud (elimina n xs) = longitud xs - n"
  oops

lemma ejercicio_C5: "longitud (coge n xs) = min n (longitud xs)"
  oops

text \<open>Ejercicio C6 [**]. Si todos cumplen \<open>p\<close>, los primeros también.\<close>
lemma ejercicio_C6: "todos p xs \<Longrightarrow> todos p (coge n xs)"
  oops

text \<open>
  Ejercicio C7 [**]. El que quedó planteado en clase: defina \<open>algun\<close>,
  que dice si algún elemento de la lista cumple \<open>p\<close>. Sustituya la
  declaración \<open>consts\<close> por su definición con \<open>fun\<close>, pruébela con
  \<open>value\<close>, y demuestre la ley de De Morgan sobre listas.
\<close>
consts algun :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"

lemma ejercicio_C7: "algun p xs = (\<not> todos (\<lambda>x. \<not> p x) xs)"
  oops

text \<open>
  Ejercicio C8 [***]. \<questiondown>Coger \<open>n\<close> elementos de una concatenación es
  concatenar lo que se coge de cada parte? Compruébelo con
  \<open>quickcheck\<close>.
\<close>
lemma "coge n (conc xs ys) = conc (coge n xs) (coge n ys)"
  oops

text \<open>
  Es falso. Sustituya \<open>undefined\<close> por la expresión correcta y
  demuestre el lema. Ojo: \<open>coge 0 xs = []\<close> no es una regla de
  \<open>simp\<close> tal cual, porque Isabelle especializó esa ecuación a
  \<open>coge 0 (v # va) = []\<close>, al solaparse con la primera (mire
  \<open>thm coge.simps\<close>). Puede necesitar demostrarla aparte.
\<close>
lemma ejercicio_C8: "coge n (conc xs ys) = conc (coge n xs) (coge undefined ys)"
  oops

text \<open>
  Ejercicio C9 [***]. \<open>elimina1\<close> y \<open>elimina\<close> calculan lo mismo.
  Primero C9a, que relaciona \<open>elimina\<close> con \<open>drop\<close> de la librería.
\<close>
lemma ejercicio_C9a: "elimina n xs = drop n xs"
  oops

lemma ejercicio_C9: "elimina1 n xs = elimina n xs"
  oops

end
