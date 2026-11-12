(* T6
   Tema 6 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T6
imports Main
begin

chapter \<open> Tema 6: Razonamiento por casos y por inducción \<close>
text \<open>
   En este tema se amplían los métodos de demostración por casos y por
   inducción iniciados en el tema anterior.
\<close>

section \<open> Razonamiento por distinción de casos \<close>

subsection \<open> Distinción de casos booleanos \<close>

text \<open>
   Ejemplo de demostración por distinción de casos booleanos:
      \<not>A \<or> A
\<close>

text \<open>La demostración estructurada es\<close>
lemma "\<not>A \<or> A"
proof cases
  assume "A"
  thus ?thesis ..
next
  assume "\<not>A"

  thus ?thesis ..
qed

text \<open>La demostración detallada es\<close>
lemma "\<not>A \<or> A"
proof cases
  assume "A"
  thus ?thesis by (rule disjI2)
next
  assume "\<not>A"
  thus ?thesis by (rule disjI1)
qed

text \<open>La demostración automática es\<close>
lemma "\<not>A \<or> A"
by auto

text \<open>
   Ejemplo de demostración por distinción de casos booleanos nominados:
      \<not>A \<or> A
\<close>

text \<open>La demostración estructurada es\<close>
lemma "\<not>A \<or> A"
proof (cases "A")
  case True
  thus ?thesis ..
next
  case False
  thus ?thesis ..
qed

text \<open>La demostración detallada es\<close>
lemma "\<not>A \<or> A"
proof (cases "A")
  case True
  thus ?thesis by (rule disjI2)
next
  case False
  thus ?thesis by (rule disjI1)

qed

text \<open>
   El método "cases" sobre una fórmula:
   \<sqdot> El método (cases F) es una abreviatura de la aplicación de la regla
        \<lbrakk>F \<Longrightarrow> Q; \<not>F \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q
   \<sqdot> La expresión "case True" es una abreviatura de F.
   \<sqdot> La expresión "case False" es una abreviatura de \<not>F.
   \<sqdot> Ventajas de "cases" con nombre:
     \<sqdot> reduce la escritura de la fórmula y
     \<sqdot> es independiente del orden de los casos.
\<close>

subsection \<open> Distinción de casos sobre otros tipos de datos \<close>

text \<open>
   Ejemplo de distinción de casos sobre listas:
   La longitud del resto de una lista es la longitud de la lista menos 1.
\<close>

text \<open>La demostración detallada es\<close>
lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis by simp
qed

text \<open>La demostración automática es\<close>
lemma "length(tl xs) = length xs - 1"
by auto

text \<open>
  Distinción de casos sobre listas:
  \<sqdot> El método de distinción de casos se activa con (cases xs) donde xs
    es del tipo lista.
  \<sqdot> "case Nil" es una abreviatura de
        "assume Nil: xs =[]".
  \<sqdot> "case Cons" es una abreviatura de
        "fix ? ?? assume Cons: xs = ? # ??"

     donde ? y ?? son variables anónimas.
\<close>

text \<open>
   Ejemplo de análisis de casos:
   El resultado de eliminar los n+1 primeros elementos de xs es el mismo
   que eliminar los n primeros elementos del resto de xs.
\<close>

text \<open>La demostración detallada es\<close>
lemma "drop (n + 1) xs = drop n (tl xs)"
proof (cases xs)
  case Nil thus "drop (n + 1) xs = drop n (tl xs)" by simp
next
  case Cons thus "drop (n + 1) xs = drop n (tl xs)" by simp
qed

text \<open>La demostración automática es\<close>
lemma "drop (n + 1) xs = drop n (tl xs)"
by (cases xs) auto

text \<open>
   La función drop está definida en la teoría List de forma que
   (drop n xs) la lista obtenida eliminando en xs} los n primeros
   elementos. Su definición es la siguiente
      drop_Nil: "drop n [] = []" |
      drop_Cons: "drop n (x#xs) = (case n of
                                     0 => x#xs |
                                     Suc(m) => drop m xs)"
\<close>

section \<open> Inducción matemática \<close>

text \<open>
  [Principio de inducción matemática]
  Para demostrar una propiedad P para todos los números naturales basta
  probar que el 0 tiene la propiedad P y que si n tiene la propiedad P,
  entonces n+1 también la tiene.
     \<lbrakk>P 0;\<And>n. P n \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P m

     En Isabelle el principio de inducción matemática está formalizado en
     el teorema nat.induct y puede verse con
        thm nat.induct
\<close>

text \<open>
  Ejemplo de demostración por inducción: Usaremos el principio de
  inducción matemática para demostrar que
     1 + 3 + ... + (2n-1) = n^2

     Definición. [Suma de los primeros impares]
     (suma_impares n) la suma de los n números impares. Por ejemplo,
        suma_impares 3 = 9
\<close>

fun suma_impares :: "nat \<Rightarrow> nat" where
  "suma_impares 0 = 0"
| "suma_impares (Suc n) = (2*(Suc n) - 1) + suma_impares n"

value "suma_impares 3"

text \<open>
   Ejemplo de demostración por inducción matemática:
   La suma de los n primeros números impares es n^2.
\<close>

text \<open>La demostración automática es\<close>
lemma "suma_impares n = n * n"
by (induct n) simp_all

text \<open>La demostración usando patrones es\<close>
lemma "suma_impares n = n * n" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P (Suc n)" by simp
qed

text \<open>

     Patrones: Cualquier fórmula seguida de (is patrón) equipara el patrón
     con la fórmula.
\<close>

text \<open>Demostración del lema anterior con patrones y razonamiento ecuacional\<close>
lemma "suma_impares n = n * n" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume HI: "?P n"
  have "suma_impares (Suc n) = (2 * (Suc n) - 1) + suma_impares n" by simp
  also have "... = (2 * (Suc n) - 1) + n * n" using HI by simp
  also have "... = n * n + 2 * n + 1" by simp
  finally show "?P (Suc n)" by simp
qed

text \<open>Demostración del lema anterior por inducción y razonamiento ecuacional\<close>
lemma "suma_impares n = n * n"
proof (induct n)
  show "suma_impares 0 = 0 * 0" by simp
next
  fix n assume HI: "suma_impares n = n * n"
  have "suma_impares (Suc n) = (2 * (Suc n) - 1) + suma_impares n" by simp
  also have "... = (2 * (Suc n) - 1) + n * n" using HI by simp
  also have "... = n * n + 2 * n + 1" by simp
  finally show "suma_impares (Suc n) = (Suc n) * (Suc n)" by simp
qed

text \<open>
   Ejemplo de definición con existenciales.
   Un número natural n es par si existe un natural m tal que n=m+m.
\<close>

definition par :: "nat \<Rightarrow> bool" where
  "par n \<equiv> \<exists>m. n=m+m"

text \<open>
   [Ejemplo de inducción y existenciales] Para todo número natural
   n, se verifica que n*(n+1) par.
\<close>

lemma
  fixes n :: "nat"
  shows "par (n*(n+1))"
proof (induct n)
  show "par (0*(0+1))" by (simp add: par_def)
next
  fix n assume "par (n*(n+1))"
  hence "\<exists>m. n*(n+1) = m+m" by (simp add:par_def)
  then obtain m where m: "n*(n+1) = m+m" by (rule exE)
  hence "(Suc n)*((Suc n)+1) = (m+n+1)+(m+n+1)" by auto
  hence "\<exists>m. (Suc n)*((Suc n)+1) = m+m" by (rule exI)
  thus "par ((Suc n)*((Suc n)+1))" by (simp add:par_def)
qed

text \<open>
   En Isabelle puede demostrarse de manera más simple un lema equivalente
   usando en lugar de la función "par" la función "even" definida en la
   teoría Parity por
      even x \<longleftrightarrow> x mod 2 = 0"
\<close>

lemma
  fixes n :: "nat"
  shows "even (n*(n+1))"
by auto

text \<open>
   Para completar la demostración basta demostrar la equivalencia de las
   funciones "par" y "even".
\<close>

lemma
  fixes n :: "nat"
  shows "par n = even n"
proof -
  have "par n = (\<exists>m. n = m+m)" by (simp add:par_def)
  thus "par n = even n" by presburger
qed

text \<open>
   En la demostración anterior hemos usado la táctica "presburger" que
   corresponde a la aritmética de Presburger.
\<close>

section \<open> Inducción estructural \<close>

text \<open>
   Inducción estructural:
   \<sqdot> En Isabelle puede hacerse inducción estructural sobre cualquier tipo
     recursivo.
   \<sqdot> La inducción matemática es la inducción estructural sobre el tipo de
     los naturales.
   \<sqdot> El esquema de inducción estructural sobre listas es
     \<sqdot> list.induct: \<lbrakk>P [];\<And>x ys. P ys \<Longrightarrow> P (x # ys)\<rbrakk> \<Longrightarrow> P zs

   \<sqdot> Para demostrar una propiedad para todas las listas basta demostrar
     que la lista vacía tiene la propiedad y que al añadir un elemento a una
     lista que tiene la propiedad se obtiene una lista que también tiene la
     propiedad.
   \<sqdot> En Isabelle el principio de inducción sobre listas está formalizado
     mediante el teorema list.induct que puede verse con
        thm list.induct
\<close>

text \<open>
   Concatenación de listas:
   En la teoría List.thy está definida la concatenación de listas (que
   se representa por @) como sigue
      append_Nil: "[]@ys = ys"
      append_Cons: "(x#xs)@ys = x#(xs@ys)"
\<close>

text \<open>
   Lema. [Ejemplo de inducción sobre listas]
   La concatenación de listas es asociativa.
\<close>

text \<open>La demostración automática es\<close>
lemma conc_asociativa_1: "xs @ (ys @ zs) = (xs @ ys) @ zs"
by (induct xs) simp_all

text \<open>La demostración estructurada es\<close>
lemma conc_asociativa: "xs @ (ys @ zs) = (xs @ ys) @ zs"
proof (induct xs)
  show "[] @ (ys @ zs) = ([] @ ys) @ zs"
  proof -
     have "[] @ (ys @ zs) = ys @ zs" by simp
     also have "... = ([] @ ys) @ zs" by simp
     finally show ?thesis .
  qed
next
  fix x xs
  assume HI: "xs @ (ys @ zs) = (xs @ ys) @ zs"
  show "(x#xs) @ (ys @ zs) = ((x#xs) @ ys) @ zs"
  proof -
     have "(x#xs) @ (ys @ zs) = x#(xs @ (ys @ zs))" by simp
     also have "... = x#((xs @ ys) @ zs)" using HI by simp
     also have "... = (x#(xs @ ys)) @ zs" by simp
     also have "... = ((x#xs) @ ys) @ zs" by simp
     finally show ?thesis .
  qed
qed

text \<open>
   Ejemplo de definición de tipos recursivos:
   Definir un tipo de dato para los árboles binarios.
\<close>

datatype 'a arbolB = Hoja "'a"
                   | Nodo "'a" "'a arbolB" "'a arbolB"

text \<open>
   Ejemplo de definición sobre árboles binarios:
   Definir la función "espejo" que aplicada a un árbol devuelve su imagen
   especular.
\<close>

fun espejo :: "'a arbolB \<Rightarrow> 'a arbolB" where
  "espejo (Hoja a) = (Hoja a)"
| "espejo (Nodo f x y) = (Nodo f (espejo y) (espejo x))"

text \<open>
   Ejemplo de demostración sobre árboles binarios:
   Demostrar que la función "espejo" es involutiva; es decir, para
   cualquier árbol t, se tiene que
      espejo (espejo(t)) = t.
\<close>

text \<open>La demostración automática es\<close>
lemma espejo_involutiva_1:
  "espejo(espejo(t)) = t"
by (induct t) auto

text \<open>La demostración estructurada es\<close>
lemma espejo_involutiva:
  "espejo(espejo(t)) = t" (is "?P t")
proof (induct t)
  fix x :: 'a show "?P (Hoja x)" by simp
next
  fix t1 :: "'a arbolB" assume h1: "?P t1"
  fix t2 :: "'a arbolB" assume h2: "?P t2"
  fix x :: 'a
  show "?P (Nodo x t1 t2)"
  proof -
     have "espejo(espejo(Nodo x t1 t2)) = espejo(Nodo x (espejo t2) (espejo t1))"
       by simp
     also have "... = Nodo x (espejo (espejo t1)) (espejo (espejo t2))" by simp
     also have "... = Nodo x t1 t2" using h1 h2 by simp
     finally show ?thesis .
 qed
qed

text \<open>
   Ejemplo. [Aplanamiento de árboles]
   Definir la función "aplana" que aplane los árboles recorriéndolos en
   orden infijo.
\<close>

fun aplana :: "'a arbolB \<Rightarrow> 'a list" where
  "aplana (Hoja a) = [a]"

| "aplana (Nodo x t1 t2) = (aplana t1)@[x]@(aplana t2)"

text \<open>
   Ejemplo. [Aplanamiento de la imagen especular] Demostrar que
      aplana (espejo t) = rev (aplana t)
\<close>

text \<open>La demostración automática es\<close>
lemma "aplana (espejo t) = rev (aplana t)"
by (induct t) auto

text \<open>La demostración estructurada es\<close>
lemma "aplana (espejo t) = rev (aplana t)" (is "?P t")
proof (induct t)
  fix x :: 'a
  show "?P (Hoja x)" by simp
next
  fix t1 :: "'a arbolB" assume h1: "?P t1"
  fix t2 :: "'a arbolB" assume h2: "?P t2"
  fix x :: 'a
  show "?P (Nodo x t1 t2)"
  proof -
     have "aplana (espejo (Nodo x t1 t2)) =
           aplana (Nodo x (espejo t2) (espejo t1))" by simp
     also have "... = (aplana(espejo t2))@[x]@(aplana(espejo t1))" by simp
     also have "... = (rev(aplana t2))@[x]@(rev(aplana t1))" using h1 h2 by simp
     also have "... = rev((aplana t1)@[x]@(aplana t2))" by simp
     also have "... = rev(aplana (Nodo x t1 t2))" by simp
     finally show ?thesis .
 qed
qed

section \<open> Heurísticas para la inducción \<close>

text \<open>
   Definición. [Definición recursiva de inversa]
   (inversa xs) la inversa de la lista xs. Por ejemplo,
      inversa [a,b,c] = [c,b,a]
\<close>

fun inversa :: "'a list \<Rightarrow> 'a list" where
  "inversa [] = []"
| "inversa (x#xs) = (inversa xs) @ [x]"

value "inversa [a,b,c]"

text \<open>
   Definición. [Definición de inversa con acumuladores]
   (inversaAc xs) es la inversa de la lista xs calculada con
   acumuladores. Por ejemplo,
      inversaAc [a,b,c]       = [c,b,a]
      inversaAcAux [a,b,c] [] = [c,b,a]
\<close>

fun inversaAcAux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inversaAcAux [] ys = ys"
| "inversaAcAux (x#xs) ys = inversaAcAux xs (x#ys)"

definition inversaAc :: "'a list \<Rightarrow> 'a list" where
  "inversaAc xs \<equiv> inversaAcAux xs []"

value "inversaAcAux [a,b,c] []"
value "inversaAc [a,b,c]"

text \<open>
   Lema. [Ejemplo de equivalencia entre las definiciones]
   La inversa de [a,b,c] es lo mismo calculada con la primera definición
   que con la segunda.
\<close>

lemma "inversaAc [a,b,c] = inversa [a,b,c]"
by (simp add: inversaAc_def)

text \<open>
   Nota. [Ejemplo fallido de demostración por inducción]
   El siguiente intento de demostrar que para cualquier lista xs, se
   tiene que "inversaAc xs = inversa xs" falla.
\<close>

lemma "inversaAc xs = inversa xs"

proof (induct xs)
  show "inversaAc [] = inversa []" by (simp add: inversaAc_def)
next
  fix a xs assume HI: "inversaAc xs = inversa xs"
  have "inversaAc (a#xs) = inversaAcAux (a#xs) []" by (simp add: inversaAc_def)
  also have "... = inversaAcAux xs [a]" by simp
  also have "... = inversa (a#xs)"  \<comment> \<open>Problema: la hipótesis de inducción no es aplicable.\<close>
oops

text \<open>
  Nota. [Heurística de generalización]
  Cuando se use demostración estructural, cuantificar universalmente las
  variables libres (o, equivalentemente, considerar las variables libres
  como variables arbitrarias).

     Lema. [Lema con generalización]
     Para toda lista ys se tiene
        inversaAcAux xs ys = (inversa xs) @ ys
\<close>

text \<open>La demostración automática es\<close>
lemma inversaAcAux_es_inversa_1:
  "inversaAcAux xs ys = (inversa xs)@ys"
by (induct xs arbitrary: ys) auto

text \<open>La demostración estructurada es\<close>
lemma inversaAcAux_es_inversa:
  "inversaAcAux xs ys = (inversa xs)@ys"
proof (induct xs arbitrary: ys)
  show "\<And>ys. inversaAcAux [] ys = (inversa [])@ys" by simp

next
  fix a xs
  assume HI: "\<And>ys. inversaAcAux xs ys = inversa xs@ys"

  show "\<And>ys. inversaAcAux (a#xs) ys = inversa (a#xs)@ys"

  proof -
     fix ys
     have "inversaAcAux (a#xs) ys = inversaAcAux xs (a#ys)" by simp
     also have "... = inversa xs@(a#ys)" using HI by simp
     also have "... = inversa (a#xs)@ys" by simp

    finally show "inversaAcAux (a#xs) ys = inversa (a#xs)@ys" by simp
  qed
qed

text \<open>
   Corolario. Para cualquier lista xs, se tiene que
      inversaAc xs = inversa xs
\<close>

corollary "inversaAc xs = inversa xs"
by (simp add: inversaAcAux_es_inversa inversaAc_def)

text \<open>
  Nota. En el paso "inversa xs@(a#ys) = inversa (a#xs)@ys" se usan
  lemas de la teoría List. Se puede observar, activando "Trace
  Simplifier" y D"|Trace Rules", que los lemas usados son
  \<sqdot> append_assoc:       (xs @ ys) @ zs = xs @ (ys @ zs)
  \<sqdot> append.append_Cons: (x#xs)@ys = x#(xs@ys)
  \<sqdot> append.append_Nil: []@ys = ys
  Los dos últimos son las ecuaciones de la definición de append.

     En la siguiente demostración se detallan los lemas utilizados.
\<close>

lemma "(inversa xs)@(a#ys) = (inversa (a#xs))@ys"
proof -
  have "(inversa xs)@(a#ys) = (inversa xs)@(a#([]@ys))"
    by (simp only:append.append_Nil)
  also have "... = (inversa xs)@([a]@ys)" by (simp only:append.append_Cons)
  also have "... = ((inversa xs)@[a])@ys" by (simp only:append_assoc)
  also have "... = (inversa (a#xs))@ys" by (simp only:inversa.simps(2))
  finally show ?thesis .
qed

section \<open> Recursión general. La función de Ackermann \<close>

text \<open>
  El objetivo de esta sección es mostrar el uso de las definiciones
  recursivas generales y sus esquemas de inducción. Como ejemplo se usa la
  función de Ackermann (se puede consultar información sobre dicha función en

     http://en.wikipedia.org/wiki/Ackermann_function).

     Definición. La función de Ackermann se define por
       A(m,n) = n+1,             si m=0,
                A(m-1,1),        si m>0 y n=0,
                A(m-1,A(m,n-1)), si m>0 y n>0
     para todo los números naturales.

     La función de Ackermann es recursiva, pero no es primitiva recursiva.
\<close>

fun ack :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ack 0 n = n+1"
| "ack (Suc m) 0 = ack m 1"
| "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"

text \<open>Ejemplo de evaluación\<close>
value "ack 2 3" (* devuelve 9 *)

text \<open>
   Esquema de inducción correspondiente a una función:
   \<sqdot> Al definir una función recursiva general se genera una regla de
     inducción. En la definición anterior, la regla generada es
     ack.induct:
        \<lbrakk>\<And>n. P 0 n;

          \<And> m. P m 1 \<Longrightarrow> P (Suc m) 0;

          \<And> m n. \<lbrakk>P (Suc m) n; P m (ack (Suc m) n)\<rbrakk> \<Longrightarrow> P (Suc m) (Suc n)\<rbrakk>

        \<Longrightarrow> P a b
\<close>

text \<open>
   Ejemplo de demostración por la inducción correspondiente a una función:
   Para todos m y n, A(m,n) > n.
\<close>

text \<open>La demostración automática es\<close>
lemma "ack m n > n"
by (induct m n rule: ack.induct) simp_all

text \<open>La demostración detallada es\<close>
lemma "ack m n > n"
proof (induct m n rule: ack.induct)
  fix n :: "nat"
  show "ack 0 n > n" by simp
next
  fix m assume "ack m 1 > 1"
  thus "ack (Suc m) 0 > 0" by simp
next
  fix m n
  assume "n < ack (Suc m) n" and
         "ack (Suc m) n < ack m (ack (Suc m) n)"
  thus "Suc n < ack (Suc m) (Suc n)" by simp
qed

text \<open>
   Nota. [Inducción sobre recursión]
   El formato para iniciar una demostración por inducción en la regla
   inductiva correspondiente a la definición recursiva de la función f m
   n es
      proof (induct m n rule:f.induct)
\<close>

section \<open> Recursión mutua e inducción \<close>

text \<open>
   Nota. [Ejemplo de definición de tipos mediante recursión cruzada]
   \<sqdot> Un árbol de tipo a es una hoja o un nodo de tipo a junto con un
     bosque de tipo a.
   \<sqdot> Un bosque de tipo a es el boque vacío o un bosque contruido añadiendo
     un árbol de tipo a a un bosque de tipo a.
\<close>

datatype 'a arbol = Hoja | Nodo "'a" "'a bosque"
     and 'a bosque = Vacio | ConsB "'a arbol" "'a bosque"

text \<open>
  Regla de inducción correspondiente a la recursión cruzada:
  La regla de inducción sobre árboles y bosques es arbol_bosque.induct:
     \<lbrakk>P1 Hoja;
       \<And> x b. P2 b \<Longrightarrow> P1 (Nodo x b);

      P2 Vacio;
      \<And> a b. \<lbrakk>P1 a; P2 b\<rbrakk> \<Longrightarrow> P2 (ConsB a b)\<rbrakk>

     \<Longrightarrow> P1 a \<and> P2 b
\<close>

text \<open>
   Ejemplos de definición por recursión cruzada:
   \<sqdot> aplana_arbol a) es la lista obtenida aplanando el árbol a.
   \<sqdot> (aplana_bosque b) es la lista obtenida aplanando el bosque b.
   \<sqdot> (map_arbol a h) es el árbol obtenido aplicando la función h a
     todos los nodos del árbol a.
   \<sqdot> (map_bosque b h) es el bosque obtenido aplicando la función h a
     todos los nodos del bosque b.
\<close>

fun
  aplana_arbol :: "'a arbol \<Rightarrow> 'a list" and
  aplana_bosque :: "'a bosque \<Rightarrow> 'a list" where
  "aplana_arbol Hoja = []"
| "aplana_arbol (Nodo x b) = x#(aplana_bosque b)"
| "aplana_bosque Vacio = []"
| "aplana_bosque (ConsB a b) = (aplana_arbol a) @ (aplana_bosque b)"

fun
  map_arbol :: "'a arbol \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b arbol" and
  map_bosque :: "'a bosque \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b bosque" where
  "map_arbol Hoja h = Hoja"
| "map_arbol (Nodo x b) h = Nodo (h x) (map_bosque b h)"
| "map_bosque Vacio h = Vacio"
| "map_bosque (ConsB a b) h = ConsB (map_arbol a h) (map_bosque b h)"

text \<open>
   Ejemplo de dempstración por inducción cruzada:
   \<sqdot> aplana_arbol (map_arbol a h) = map h (aplana_arbol a)
   \<sqdot> aplana_bosque (map_bosque b h) = map h (aplana_bosque b)
\<close>

text \<open>La demostración automática es\<close>
lemma "aplana_arbol (map_arbol a h) = map h (aplana_arbol a)
     \<and> aplana_bosque (map_bosque b h) = map h (aplana_bosque b)"

by (induct_tac a and b) auto

text \<open>La demostración detallada es\<close>
lemma "aplana_arbol (map_arbol a h) = map h (aplana_arbol a)
      \<and> aplana_bosque (map_bosque b h) = map h (aplana_bosque b)"
proof (induct_tac a and b)
  show "aplana_arbol (map_arbol Hoja h) = map h (aplana_arbol Hoja)" by simp
next
  fix x b
  assume HI: "aplana_bosque (map_bosque b h) = map h (aplana_bosque b)"
  have "aplana_arbol (map_arbol (Nodo x b) h)
         = aplana_arbol (Nodo (h x) (map_bosque b h))" by simp
  also have "... = (h x)#(aplana_bosque (map_bosque b h))" by simp
  also have "... = (h x)#(map h (aplana_bosque b))" using HI by simp
  also have "... = map h (aplana_arbol (Nodo x b))" by simp
  finally show "aplana_arbol (map_arbol (Nodo x b) h)
                 = map h (aplana_arbol (Nodo x b))" .
next
  show "aplana_bosque (map_bosque Vacio h) = map h (aplana_bosque Vacio)"
     by simp
next
  fix a b
  assume HI1: "aplana_arbol (map_arbol a h) = map h (aplana_arbol a)"
      and HI2: "aplana_bosque (map_bosque b h) = map h (aplana_bosque b)"
  have "aplana_bosque (map_bosque (ConsB a b) h)
         = aplana_bosque (ConsB (map_arbol a h) (map_bosque b h))" by simp
  also have "... = aplana_arbol(map_arbol a h)@aplana_bosque(map_bosque b h)"
     by simp
  also have "... = (map h (aplana_arbol a))@(map h (aplana_bosque b))"
     using HI1 HI2 by simp
  also have "... = map h (aplana_bosque (ConsB a b))" by simp
  finally show "aplana_bosque (map_bosque (ConsB a b) h)
                 = map h (aplana_bosque (ConsB a b))" by simp
qed

end
