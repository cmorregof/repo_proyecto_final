(* T8a
   Tema 8 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T8a
imports Main
begin

chapter \<open> Tema 8: Conjuntos, funciones y relaciones \<close>
section \<open> Conjuntos \<close>

subsection \<open> Operaciones con conjuntos \<close>

text \<open>
  Nota. La teoría elemental de conjuntos es HOL/Set.thy.

  Nota. En un conjunto todos los elemento son del mismo tipo (por
  ejemplo, del tipo \<tau> ) y el conjunto tiene tipo (en el ejemplo, "\<tau> set").

  Reglas de la intersección:
  \<sqdot> IntI: \<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> c \<in> A \<inter> B
  \<sqdot> IntD1: c \<in> A \<inter> B \<Longrightarrow> c \<in> A
  \<sqdot> IntD2: c \<in> A \<inter> B \<Longrightarrow> c \<in> B

  Nota. Propiedades del complementario:
  \<sqdot> Compl_iff: (c \<in> - A) = (c \<notin> A)
  \<sqdot> Compl_Un: - (A \<union> B) = - A \<inter> - B

  Nota. El conjunto vacío se representa por {} y el universal por UNIV.

     Nota. Propiedades de la diferencia y del complementario:
     \<sqdot> Diff_disjoint:   A \<inter> (B - A) = {}
     \<sqdot> Compl_partition: A \<union> - A = UNIV

     Nota. Reglas de la relación de subconjunto:
     \<sqdot> subsetI: (\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B

     \<sqdot> subsetD: \<lbrakk>A \<subseteq> B; c \<in> A\<rbrakk> \<Longrightarrow> c \<in> B
\<close>

text \<open>
   Ejemplo: A \<union> B \<subseteq> C syss A \<subseteq> C \<and> B \<subseteq> C.
\<close>

lemma "(A \<union> B \<subseteq> C) = (A \<subseteq> C \<and> B \<subseteq> C)"
by blast

text \<open>
   Ejemplo: A \<subseteq> -B syss B \<subseteq> -A.
\<close>

lemma "(A \<subseteq> -B) = (B \<subseteq> -A)"
by blast

text \<open>
  Principio de extensionalidad de conjuntos:
  \<sqdot> set_ext: (\<And>x. (x \<in> A) = (x \<in> B)) \<Longrightarrow> A = B

     Reglas de la igualdad de conjuntos:
     \<sqdot> equalityI: \<lbrakk>A \<subseteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> A = B
     \<sqdot> equalityE: \<lbrakk>A = B; \<lbrakk>A \<subseteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P
\<close>

text \<open>
   Lema. [Analogía entre intersección y conjunción]
   "x \<in> A \<inter> B" syss "x \<in> A" y "x \<in> B".
\<close>

lemma "(x \<in> A \<inter> B) = (x \<in> A \<and> x \<in> B)"
by simp

text \<open>
   Lema. [Analogía entre unión y disyunción]
   x \<in> A \<union> B syss x \<in> A ó x \<in> B.
\<close>

lemma "(x \<in> A \<union> B) = (x \<in> A \<or> x \<in> B)"
by simp

text \<open>
   Lema. [Analogía entre subconjunto e implicación]
   A \<subseteq> B syss para todo x, si x \<in> A entonces x \<in> B.
\<close>

lemma "(A \<subseteq> B) = (\<forall> x. x \<in> A \<longrightarrow> x \<in> B)"
by auto

text \<open>
   Lema. [Analogía entre complementario y negación]
   x pertenece al complementario de A syss x no pertenece a A.
\<close>

lemma "(x \<in> -A) = (x \<notin> A)"
by simp

subsection \<open> Notación de conjuntos finitos
\<close>

text \<open>
  Nota. La teoría de conjuntos finitos es HOL/Finite_Set.thy.

     Nota. Los conjuntos finitos se definen por inducción a partir de las
     siguientes reglas inductivas:
     \<sqdot> El conjunto vacío es un conjunto finito.
       \<sqdot> emptyI: "finite {}"
     \<sqdot> Si se le añade un elemento a un conjunto finito se obtiene otro
       conjunto finito.
       \<sqdot> insertI: "finite A \<Longrightarrow> finite (insert a A)"

     A continuación se muestran ejemplos de conjuntos finitos.
\<close>

lemma
  "insert 2 {} = {2} \<and>
   insert 3 {2} = {2,3} \<and>
   insert 2 {2,3} = {2,3} \<and>
   {2,3} = {3,2,3,2,2}"
by auto

text \<open>
   Nota. Los conjuntos finitos se representan con la notación conjuntista
   habitual: los elementos entre llaves y separados por comas.
\<close>

text \<open>
   Ejemplo: {a,b} \<union> {c,d} = {a,b,c,d}
\<close>

lemma "{a,b} \<union> {c,d} = {a,b,c,d}"
by blast

text \<open>
   Ejemplo de conjetura falsa y su refutación.
\<close>

lemma "{a,b} \<inter> {b,c} = {b}"
nitpick
oops

text \<open>
   Ejemplo con la conjetura corregida.
\<close>

lemma "{a,b} \<inter> {b,c} = (if a=c then {a,b} else {b})"
by auto

text \<open>
  Sumas y productos de conjuntos finitos:
  \<sqdot> (sum f A) es la suma de la aplicación de f a los elementos del
    conjunto finito A,
  \<sqdot> (prod f A) es producto de la aplicación de f a los elementos del

       conjunto finito A,
     \<sqdot> \<Sum>A es la suma de los elementos del conjunto finito A,
     \<sqdot> \<Prod>A es el producto de los elementos del conjunto finito A.

     Ejemplos de definiciones recursivas sobre conjuntos finitos:
     Sea A un conjunto finito de números naturales.
     \<sqdot> sumaConj A es la suma de los elementos A.
     \<sqdot> productoConj A es el producto de los elementos de A.
     \<sqdot> sumaCuadradosConj A es la suma de los cuadrados de los elementos A.
\<close>

definition sumaConj :: "nat set \<Rightarrow> nat" where
  "sumaConj S \<equiv> \<Sum>S"

value "sumaConj {2,5,3}"  \<comment> \<open>= 10\<close>
definition productoConj :: "nat set \<Rightarrow> nat" where
  "productoConj S \<equiv> \<Prod>S"

definition sumaCuadradosConj :: "nat set \<Rightarrow> nat" where
  "sumaCuadradosConj S \<equiv> sum (\<lambda>x. x*x) S"

value "sumaCuadradosConj {2,5,3}"  \<comment> \<open>= 38\<close>
text \<open>
   Nota. Para simplificar lo que sigue, declaramos las anteriores
   definiciones como reglas de simplificación.
\<close>

declare sumaConj_def[simp]
declare productoConj_def[simp]
declare sumaCuadradosConj_def[simp]

text \<open>
   Ejemplos de evaluación de las anteriores definiciones recursivas.
\<close>

lemma
  "sumaConj {1,2,3,4} = 10 \<and>
   productoConj {1,2,3} = productoConj {3,2} \<and>

   sumaCuadradosConj {1,2,3,4} = 30"
by simp

text \<open>
   Inducción sobre conjuntos finitos: Para demostrar que todos los
   conjuntos finitos tienen una propiedad P basta probar que
   \<sqdot> El conjunto vacío tiene la propiedad P.
   \<sqdot> Si a un conjunto finito que tiene la propiedad P se le añade un
     nuevo elemento, el conjunto obtenido sigue teniendo la propiedad P.
   En forma de regla
   \<sqdot> finite_induct: \<lbrakk>finite F;
                       P {};
                       \<And> x F. \<lbrakk>finite F; x \<notin> F; P F\<rbrakk> \<Longrightarrow> P ({x} \<union> F)\<rbrakk>

                     \<Longrightarrow> P F
\<close>

text \<open>
   Ejemplo de inducción sobre conjuntos finitos: Sea S un conjunto finito
   de números naturales. Entonces todos los elementos de S son menores o
   iguales que la suma de los elementos de S.
\<close>

text \<open>La demostración automática es\<close>
lemma "finite S \<Longrightarrow> \<forall>x\<in>S. x \<le> sumaConj S"
by (induct rule: finite_induct) auto

text \<open>La demostración estructurada es\<close>
lemma sumaConj_acota:
  "finite S \<Longrightarrow> \<forall>x\<in>S. x \<le> sumaConj S"
proof (induct rule: finite_induct)
  show "\<forall>x \<in> {}. x \<le> sumaConj {}" by simp
next
  fix x and F
  assume fF: "finite F"
      and xF: "x \<notin> F"
      and HI: "\<forall> x\<in>F. x \<le> sumaConj F"
  show "\<forall>y \<in> insert x F. y \<le> sumaConj (insert x F)"
  proof
     fix y
     assume "y \<in> insert x F"

    show "y \<le> sumaConj (insert x F)"
    proof (cases "y = x")
      assume "y = x"
      hence "y \<le> x + (sumaConj F)" by simp
      also have "... = sumaConj (insert x F)" using fF xF by simp
      finally show ?thesis .
    next
      assume "y \<noteq> x"
      hence "y \<in> F" using `y \<in> insert x F` by simp
      hence "y \<le> sumaConj F" using HI by blast
      also have "... \<le> x + (sumaConj F)" by simp
      also have "... = sumaConj (insert x F)" using fF xF by simp
      finally show ?thesis .
    qed
  qed
qed

subsection \<open> Definiciones por comprensión \<close>

text \<open>
  El conjunto de los elementos que cumple la propiedad P se representa
  por {x. P}.

     Reglas de comprensión (relación entre colección y pertenencia):
     \<sqdot> mem_Collect_eq: (a \<in> {x. P x}) = P a
     \<sqdot> Collect_mem_eq: {x. x \<in> A} = A
\<close>

text \<open>
   Ejemplo de comprensión: {x. P x \<or> x \<in> A} = {x. P x} \<union> A
\<close>

lemma "{x. P x \<or> x \<in> A} = {x. P x} \<union> A"
by blast

text \<open>
   Ejemplo de comprensión: {x. P x \<longrightarrow> Q x} = -{x. P x} \<union> {x. Q x}
\<close>

lemma "{x. P x \<longrightarrow> Q x} = -{x. P x} \<union> {x. Q x}"

by blast

text \<open>
   Ejemplo con la sintaxis general de comprensión.
      {p*q | p q. p \<in> prime \<and> q \<in> prime} =
      {z. \<exists>p q. z = p*q \<and> p \<in> prime \<and> q \<in> prime}
\<close>

lemma
  "{p*q | p q. p \<in> prime \<and> q \<in> prime} =
   {z. \<exists>p q. z = p*q \<and> p \<in> prime \<and> q \<in> prime}"
by blast

text \<open>
   En HOL, la notación conjuntista es azúcar sintáctica:
   \<sqdot> x \<in> A es equivalente a A(x).
   \<sqdot> {x. P} es equivalente a \<lambda>x. P.
\<close>

text \<open>
   Ejemplo de definición por comprensión: El conjunto de los pares es el
   de los números n para los que existe un m tal que n = 2*m.
\<close>

definition Pares :: "nat set" where
  "Pares \<equiv> {n. \<exists>m. n = 2*m }"

text \<open>
   Ejemplo. Los números 2 y 34 son pares.
\<close>

lemma
  "2 \<in> Pares \<and>
   34 \<in> Pares"
by (simp add: Pares_def)

text \<open>
   Definición. El conjunto de los impares es el de los números n para los
   que existe un m tal que n = 2*m + 1.
\<close>

definition Impares :: "nat set" where
  "Impares \<equiv> {n. \<exists>m. n = 2*m + 1 }"

text \<open>
   Ejemplo con las reglas de intersección y comprensión: El conjunto de
   los pares es disjunto con el de los impares.
\<close>

text \<open>La demostración detallada es\<close>
lemma "x \<notin> (Pares \<inter> Impares)"
proof
  fix x assume S: "x \<in> (Pares \<inter> Impares)"
  hence "x \<in> Pares" by (rule IntD1)
  hence "\<exists>m. x = 2 * m" by (simp only: Pares_def mem_Collect_eq)
  then obtain p where p: "x = 2 * p" ..
  from S have "x \<in> Impares" by (rule IntD2)
  hence "\<exists> m. x = 2 * m + 1" by (simp only: Impares_def mem_Collect_eq)
  then obtain q where q: "x = 2 * q + 1" ..
  from p and q show "False" by arith
qed

text \<open>La demostración estructurada es\<close>
lemma "x \<notin> (Pares \<inter> Impares)"
proof
  fix x assume S: "x \<in> (Pares \<inter> Impares)"
  hence "x \<in> Pares" ..
  hence "\<exists>m. x = 2 * m" by (simp only: Pares_def mem_Collect_eq)
  then obtain p where p: "x = 2 * p" ..
  from S have "x \<in> Impares" ..
  hence "\<exists> m. x = 2 * m + 1" by (simp only: Impares_def mem_Collect_eq)
  then obtain q where q: "x = 2 * q + 1" ..
  from p and q show "False" by arith
qed

text \<open>La demostración automática es\<close>
lemma "x \<notin> (Pares \<inter> Impares)"
by (auto simp add: Pares_def Impares_def mem_Collect_eq, arith)

subsection \<open> Cuantificadores acotados \<close>

text \<open>
  Reglas de cuantificador universal acotado ("bounded"):
  \<sqdot> ballI: (\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x\<in>A. P x

  \<sqdot> bspec: \<lbrakk>\<forall>x\<in>A. P x; x \<in> A\<rbrakk> \<Longrightarrow> P x

     Reglas de cuantificador existencial acotado ("bounded"):
     \<sqdot> bexI: \<lbrakk>P x; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. P x
     \<sqdot> bexE: \<lbrakk>\<exists>x\<in>A. P x;\<And>x. \<lbrakk>x \<in> A; P x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q

     Reglas de la unión indexada:
     \<sqdot> UN_iff: (b \<in> (\<Union>x\<in>A. B x)) = (\<exists>x\<in>A. b \<in> B x)

     \<sqdot> UN_I:   \<lbrakk>a \<in> A; b \<in> B a\<rbrakk> \<Longrightarrow> b \<in> (\<Union>x\<in>A. B x)

     \<sqdot> UN_E:   \<lbrakk>b \<in> ( x\<in>A. B x); x. \<lbrakk>x \<in> A; b \<in> B x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
                      S            V

     Reglas de la unión de una familia:
     \<sqdot> Union_def: S = ( x\<in>S. x)
                  S     S

     \<sqdot> Union_iff: (A \<in>\<Union>C) = (\<exists>X\<in>C. A \<in> X)

     Reglas de la intersección indexada:
     \<sqdot> INT_iff: (b \<in> (\<Inter>x\<in>A. B x)) = (\<forall>x\<in>A. b \<in> B x)

     \<sqdot> INT_I:   ( x. x \<in> A \<Longrightarrow> b \<in> B x) \<Longrightarrow> b \<in> ( x\<in>A. B x)
                  V                              T

     \<sqdot> INT_E:   \<lbrakk>b \<in> (\<Inter>x\<in>A. B x); b \<in> B a \<Longrightarrow> R; a \<notin> A \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R

     Reglas de la intersección de una familia:
     \<sqdot> Inter_def: S = ( x\<in>S. x)
                  T     T

     \<sqdot> Inter_iff: (A \<in>\<Inter>C) = (\<forall>X\<in>C. A \<in> X)

     Abreviaturas:
     \<sqdot> "Collect P" es lo mismo que "{x. P}".
     \<sqdot> "All P"     es lo mismo que "\<forall>x. P x".
     \<sqdot> "Ex P"      es lo mismo que "\<exists>x. P x".
     \<sqdot> "Ball A P" es lo mismo que "\<forall>x\<in>A. P x".
     \<sqdot> "Bex A P"   es lo mismo que "\<exists>x\<in>A. P x".
\<close>

subsection \<open> Conjuntos finitos y cardinalidad \<close>

text \<open>
  El número de elementos de un conjunto finito A es el cardinal de A y

     se representa por "card A".
\<close>

text \<open>
   Ejemplos de cardinales de conjuntos finitos.
\<close>

lemma
  "card {} = 0 \<and>
   card {4} = 1 \<and>
   card {4,1} = 2 \<and>
   x \<noteq> y \<Longrightarrow> card {x,y} = 2"
by simp

text \<open>
   Propiedades de cardinales:
   \<sqdot> Cardinal de la unión de conjuntos finitos:
     card_Un_Int: \<lbrakk>finite A; finite B\<rbrakk>
                  \<Longrightarrow> card A + card B = card (A \<union> B) + card (A \<inter> B)"
   \<sqdot> Cardinal del conjunto potencia:
     card_Pow: finite A \<Longrightarrow> card (Pow A) = 2 ^ card A
\<close>

section \<open> Funciones \<close>

text \<open>
   La teoría de funciones es HOL/Fun.thy.
\<close>

subsection \<open> Nociones básicas de funciones \<close>

text \<open>
  Principio de extensionalidad para funciones:
  \<sqdot> ext: (\<And>x. f x = g x) \<Longrightarrow> f = g

     Actualización de funciones
     \<sqdot> fun_upd_apply: (f(x := y)) z = (if z = x then y else f z)
     \<sqdot> fun_upd_upd:   f(x := y, x := z) = f(x := z)

     Función identidad

     \<sqdot> id_def: id \<equiv> \<lambda>x. x

     Composición de funciones:
     \<sqdot> o_def: f \<circ> g = (\<lambda>x. f (g x))

     Asociatividad de la composición:
     \<sqdot> o_assoc: f \<circ> (g \<circ> h) = (f \<circ> g) \<circ> h
\<close>

subsection \<open> Funciones inyectivas, suprayectivas y biyectivas \<close>

text \<open>
  Función inyectiva sobre A:
  \<sqdot> inj_on_def: inj_on f A \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y

     Nota. "inj f" es una abreviatura de "inj_on f UNIV".

     Función suprayectiva:
     \<sqdot> surj_def: surj f \<equiv> \<forall>y. \<exists>x. y = f x

     Función biyectiva:
     \<sqdot> bij_def: bij f \<equiv> inj f \<and> surj f

     Propiedades de las funciones inversas:
     \<sqdot> inv_f_f:      inj f \<Longrightarrow> inv f (f x) = x
     \<sqdot> surj_f_inv_f: surj f \<Longrightarrow> f (inv f y) = y
     \<sqdot> inv_inv_eq:   bij f \<Longrightarrow> inv (inv f) = f

     Igualdad de funciones (por extensionalidad):
     \<sqdot> fun_eq_iff: (f = g) = (\<forall>x. f x = g x)
\<close>

text \<open>
   Ejemplo de lema de demostración de propiedades de funciones: Una
   función inyectiva puede cancelarse en el lado izquierdo de la
   composición de funciones.
\<close>

text \<open>La demostración detallada es\<close>
lemma

  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) = (g = h)"
proof
  assume "f \<circ> g = f \<circ> h"
  show "g = h"
  proof
     fix x
     have "(f \<circ> g)(x) = (f \<circ> h)(x)" using `f \<circ> g = f \<circ> h` by simp
     hence "f(g(x)) = f(h(x))" by simp
     thus "g(x) = h(x)" using `inj f` by (simp add:inj_on_def)
  qed
next
  assume "g = h"
  show "f \<circ> g = f \<circ> h"
  proof
     fix x
     have "(f \<circ> g) x = f(g(x))" by simp
     also have "... = f(h(x))" using `g = h` by simp
     also have "... = (f \<circ> h) x" by simp
     finally show "(f \<circ> g) x = (f \<circ> h) x" by simp
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) = (g = h)"
proof
  assume "f \<circ> g = f \<circ> h"
  thus "g = h" using `inj f` by (simp add: inj_on_def fun_eq_iff)
next
  assume "g = h"
  thus "f \<circ> g = f \<circ> h" by auto
qed

text \<open>La demostración automática es\<close>
lemma
  assumes "inj f"
  shows "(f \<circ> g = f \<circ> h) = (g = h)"
using assms

by (auto simp add: inj_on_def fun_eq_iff)

subsubsection \<open> Función imagen \<close>

text \<open>
  Imagen de un conjunto mediante una función:
  \<sqdot> image_def: f \<turnstile> A = {y. (\<exists>x\<in>A. y = f x)

     Propiedades de la imagen:
     \<sqdot> image_compose: (f \<circ> g)`r = f`g`r
     \<sqdot> image_Un:      f`(A \<union> B) = f`A \<union> f`B
     \<sqdot> image_Int:     inj f \<Longrightarrow> f`(A \<inter> B) = f`A \<inter> f`B"
\<close>

text \<open>
   Ejemplo de demostración de propiedades de la imagen:
      f`A \<union> g`A = (\<Union>x\<in>A. {f x, g x})

\<close>

lemma "f`A \<union> g`A = (\<Union>x\<in>A. {f x, g x})"

by auto

text \<open>
   Ejemplo de demostración de propiedades de la imagen:
      f`{(x,y). P x y} = {f(x,y) | x y. P x y}
\<close>

lemma "f`{(x,y). P x y} = {f(x,y) | x y. P x y}"
by auto

text \<open>
  El rango de una función ("range f") es la imagen del universo ("f`UNIV").

     Imagen inversa de un conjunto:
     \<sqdot> vimage_def: f -` B \<equiv> {x. f x : B}

     Propiedad de la imagen inversa de un conjunto:
     \<sqdot> vimage_Compl: f -` (-A) = -(f -` A)
\<close>

section \<open> Relaciones \<close>

subsection \<open> Relaciones básicas \<close>

text \<open>
  La teoría de relaciones es HOL/Relation.thy.

     Las relaciones son conjuntos de pares.

     Relación identidad:
     \<sqdot> Id_def: Id \<equiv> {p. \<exists>x. p = (x,x)}

     Composición de relaciones:
     \<sqdot> rel_comp_def: r O s \<equiv> {(x,z). \<exists>y. (x, y) \<in> r \<and> (y, z) \<in> s}

     Propiedades:
     \<sqdot> R_O_Id:        R O Id = R
     \<sqdot> rel_comp_mono: \<lbrakk>r' \<subseteq> r; s' \<subseteq> s\<rbrakk> \<Longrightarrow> (r' O s') \<subseteq> (r O s)

     Imagen inversa de una relación:
     \<sqdot> converse_iff: ((a,b) \<in> r^^-1) = ((b,a) \<in> r)

     Propiedad de la imagen inversa de una relación:
     \<sqdot> converse_rel_comp: (r O s)^-1 = s^-1 O r^-1

     Imagen de un conjunto mediante una relación:
     \<sqdot> Image_iff: (b \<in> r``A) = (\<exists>x:A. (x, b) \<in> r)

     Dominio de una relación:
     \<sqdot> Domain_iff: (a \<in> Domain r) = (\<exists>y. (a, y) \<in> r)

     Rango de una relación:
     \<sqdot> Range_iff: (a \<in> Range r) = (\<exists>y. (y,a) \<in> r)
\<close>

subsection \<open> Clausura reflexiva y transitiva \<close>

text \<open>
  La teoría de la clausura reflexiva y transitiva de una relación es
  HOL/Transitive_Closure.thy.

     Potencias de relaciones:
     \<sqdot> R ^^ 0 = Id
     \<sqdot> R ^^ (Suc n) = (R ^^ n) O R

     La clausura reflexiva y transitiva de la relación r es la menor
     solución de la ecuación:
     \<sqdot> rtrancl_unfold: r^* = Id \<union> (r^* O r)

     Propiedades básicas de la clausura reflexiva y transitiva:
     \<sqdot> rtrancl_refl:   (a,a) \<in> r^*
     \<sqdot> r_into_rtrancl: p \<in> r \<Longrightarrow> p \<in> r^*
     \<sqdot> rtrancl_trans: \<lbrakk>(a,b) \<in> r^*; (b,c) \<in> r^*\<rbrakk> \<Longrightarrow> (a,c) \<in> r^*

     Inducción sobre la clausura reflexiva y transitiva
     \<sqdot> rtrancl_induct: \<lbrakk>(a,b) \<in> r^*;
                          P b;
                          \<And> y z. \<lbrakk>(y,z) \<in> r; (z,b) \<in> r^*; P z\<rbrakk> \<Longrightarrow> P y\<rbrakk>

                        \<Longrightarrow> P a

     Idempotencia de la clausura reflexiva y transitiva:
     \<sqdot> rtrancl_idemp: (r^* )^* = r^*

     Reglas de introducción de la clausura transitiva:
     \<sqdot> r_into_trancl': p \<in> r \<Longrightarrow> p \<in> r^+
     \<sqdot> trancl_trans:   \<lbrakk>(a,b) \<in> r^+; (b,c) \<in> r^+\<rbrakk> \<Longrightarrow> (a,c) \<in> r^+

     Ejemplo de propiedad:
     \<sqdot> trancl_converse: (r\<inverse>)^+ = (r^+)\<inverse>
\<close>

subsection \<open> Una demostración elemental \<close>

text \<open>
   Se desea demostrar que la clausura reflexiva y transitiva conmuta con
   la inversa (cl_rtrans_inversa). Para demostrarlo introducimos dos lemas
   auxiliares: cl_rtrans_inversaD y cl_rtrans_inversaI.
\<close>

text \<open>La demostración detallada del primer lema es\<close>
lemma cl_rtrans_inversaD:
  "(x,y) \<in> (r\<inverse>)\<^sup>* \<Longrightarrow> (y,x) \<in> r\<^sup>*"
proof (induct rule:rtrancl_induct)
  show "(x,x) \<in> r\<^sup>*" by (rule rtrancl_refl)
next
  fix y z
  assume "(x,y) \<in> (r\<inverse>)\<^sup>*" and "(y,z) \<in> r\<inverse>" and "(y,x) \<in> r\<^sup>*"
  show "(z,x) \<in> r\<^sup>*"
  proof (rule rtrancl_trans)
     show "(z,y) \<in> r\<^sup>*" using `(y,z) \<in> r\<inverse>` by simp
  next
     show "(y,x) \<in> r\<^sup>*" using `(y,x) \<in> r\<^sup>*` by simp
  qed
qed

text \<open>La demostración automática del primer lema es\<close>
lemma cl_rtrans_inversaD2:
  "(x,y) \<in> (r\<inverse>)\<^sup>* \<Longrightarrow> (y,x) \<in> r\<^sup>*"
by (induct rule: rtrancl_induct)
   (auto simp add: rtrancl_refl rtrancl_trans)

text \<open>La demostración detallada del segundo lema es\<close>
lemma cl_rtrans_inversaI:
  "(y,x) \<in> r\<^sup>* \<Longrightarrow> (x,y) \<in> (r\<inverse>)\<^sup>*"
proof (induct rule: rtrancl_induct)
  show "(y,y) \<in> (r\<inverse>)\<^sup>*" by (rule rtrancl_refl)
next
  fix u z
  assume "(y,u) \<in> r\<^sup>*" and "(u,z) \<in> r" and "(u,y) \<in> (r\<inverse>)\<^sup>*"
  show "(z,y) \<in> (r\<inverse>)\<^sup>*"
  proof (rule rtrancl_trans)
     show "(z,u) \<in> (r\<inverse>)\<^sup>*" using `(u,z) \<in> r` by auto
  next
     show "(u,y) \<in> (r\<inverse>)\<^sup>*" using `(u,y) \<in> (r\<inverse>)\<^sup>*` by simp
  qed
qed

text \<open>La demostración detalla del teorema es\<close>
theorem cl_rtrans_inversa:
  "(r\<inverse>)\<^sup>* = (r\<^sup>*)\<inverse> "

proof
  show "(r\<inverse>)\<^sup>* \<subseteq> (r\<^sup>*)\<inverse> " by (auto simp add:cl_rtrans_inversaD)
next
  show "(r\<^sup>*)\<inverse> \<subseteq> (r\<inverse>)\<^sup>*" by (auto simp add:cl_rtrans_inversaI)
qed

text \<open>La demostración automática del teorema es\<close>
theorem "(r\<inverse>)\<^sup>* = (r\<^sup>*)\<inverse> "
by (auto intro: cl_rtrans_inversaI dest: cl_rtrans_inversaD)

section \<open> Relaciones bien fundamentadas e inducción \<close>

text \<open>
  La teoría de las relaciones bien fundamentadas es
  HOL/Wellfounded_Relations.thy.

     La relación-objeto "less_than" es el orden de los naturales definido por
     \<sqdot> less_than = pred_nat^+
     donde pred_nat está definida por
     \<sqdot> pred_nat = {(m, n). n = Suc m}

     La caracterización de less_than es
     \<sqdot> less_than_iff: ((x,y) \<in> less_than) = (x < y)

     La relación less_than está bien fundamentada
     \<sqdot> wf_less_than: wf less_than

     Notas sobre medidas:
     \<sqdot> Imagen inversa de una relación mediante una función:
       \<sqdot> inv_image_def: inv_image r f \<equiv> {(x,y). (f x,f y) \<in> r}
     \<sqdot> Conservación de la buena fundamentación:
       \<sqdot> wf_inv_image: wf r \<Longrightarrow> wf (inv_image r f)
     \<sqdot> Definición de la medida:
       \<sqdot> measure_def: measure \<equiv> inv_image less_than
     \<sqdot> Buena fundamentación de la medida:
       \<sqdot> wf_measure: wf (measure f)
\<close>

text \<open>
  Notas sobre el producto lexicográfico:

     \<sqdot> Definición del producto lexicográfico (lex_prod_def):
       ra <*lex*> rb \<equiv> {((a,b),(a',b')). (a,a') \<in> ra \<or>
                                          (a = a' \<and> (b,b') \<in> rb)}
     \<sqdot> Conservación de la buena fundamentación:
       \<sqdot> wf_lex_prod: \<lbrakk>wf ra; wf rb\<rbrakk> \<Longrightarrow> wf (ra <*lex*> rb)

     El orden de multiconjuntos está en la teoría HOL/Library/Multiset.thy.

     Inducción sobre relaciones bien fundamentadas:
     \<sqdot> wf_induct: \<lbrakk>wf r; x. ( y. (y,x) \<in> r \<Longrightarrow> P y) \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P a
                         V    V

\<close>

section \<open> Puntos fijos \<close>

text \<open>
  La teoría de los puntos fijos se aplican a las funciones monótonas.

     Las funciones monótonas está definida (en Orderings.thy) por
     \<sqdot> mono_def: mono f \<equiv> \<forall>A B. A \<le> B \<longrightarrow> f A \<le> f B

     Las reglas de introducción y eliminación de la monotonicidad son:
     . monoI: ( A\<And>B. A \<le> B \<Longrightarrow> f A \<le> f B) \<Longrightarrow> mono f

     \<sqdot> monoD: \<lbrakk>mono f \<Longrightarrow> A \<le> B\<rbrakk> \<Longrightarrow> f A \<le> f B

     El menor punto fijo de un operador está definido en la teoría
     Inductive.thy, para los retículos completos, por
     \<sqdot> lfp_def: lfp f = Inf {u. f u \<le> u}

     El menor punto fijo de una función monótona es un punto fijo:
     \<sqdot> lfp_unfold: mono f \<Longrightarrow> lfp f = f (lfp f)

     La regla de inducción del menor punto fijo es
     \<sqdot> lfp_induct_set: \<lbrakk> a \<in> lfp(f);
                           mono(f);
                             x. \<lbrakk> x \<in> f(lfp(f)   {x. P(x)}) \<rbrakk> \<Longrightarrow> P(x) \<rbrakk>
                           V                    T

                        \<Longrightarrow> P(a)
\<close>

text \<open>
  El mayor punto fijo de un operador está definido en la teoría

     Inductive.thy, para los retículos completos, por
     \<sqdot> gfp_def: gfp f = Sup {u. u \<le> f u}

     El menor punto fijo de una función monótona es un punto fijo:
     \<sqdot> gfp_unfold: mono f \<Longrightarrow> gfp f = f (gfp f)

     La regla de inducción del menor punto fijo es
     \<sqdot> coinduct_set: \<lbrakk> mono(f);
                         a \<in> X;
                         X \<subseteq> f(X \<Union> gfp(f)) \<rbrakk>

                      \<Longrightarrow> a \<in> gfp(f)
\<close>

end
