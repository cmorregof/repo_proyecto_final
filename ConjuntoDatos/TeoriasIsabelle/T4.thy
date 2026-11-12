(* T4
   Tema 4 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T4
imports Main
begin

chapter \<open> Tema 4: Programación funcional en Isabelle \<close>
section \<open> Introducción \<close>

text \<open>
  En este tema se presenta el lenguaje funcional que está
  incluido en Isabelle. El lenguaje funcional es muy parecido a
  Haskell. \<close>

section \<open> Números naturales, enteros y booleanos \<close>

text \<open> En Isabelle están definidos los número naturales con la sintaxis
  de Peano usando dos constructores: 0 (cero) y Suc (el sucesor).

  Los números como el 1 son abreviaturas de los correspondientes en la
  notación de Peano, en este caso "Suc 0".

  El tipo de los números naturales es nat.

  Por ejemplo, el siguiente del 0 es el 1. \<close>

value "Suc 0"  \<comment> \<open>= 1\<close>
text \<open> En Isabelle está definida la suma de los números naturales:
  (x + y) es la suma de x e y.

     Por ejemplo, la suma de los números naturales 1 y 2 es el número
     natural 3. \<close>

value "(1::nat) + 2"  \<comment> \<open>= 3\<close>
text \<open> La notación del par de dos puntos se usa para asignar un tipo a
  un término (por ejemplo, (1::nat) significa que se considera que 1 es
  un número natural).

     En Isabelle está definida el producto de los números naturales:
     (x * y) es el producto de x e y.

     Por ejemplo, el producto de los números naturales 2 y 3 es el número
     natural 6. \<close>

value "(2::nat) * 3"  \<comment> \<open>= 6\<close>
text \<open> En Isabelle está definida la división de números naturales:
  (n div m) es el cociente entero de x entre y.

     Por ejemplo, la división natural de 7 entre 3 es 2. \<close>

value "(7::nat) div 3"  \<comment> \<open>= 2\<close>
text \<open> En Isabelle está definida el resto de división de números
  naturales: (n mod m) es el resto de dividir n entre m.

     Por ejemplo, el resto de dividir 7 entre 3 es 1. \<close>

value "(7::nat) mod 3"  \<comment> \<open>= 1\<close>
text \<open> En Isabelle también están definidos los números enteros. El tipo
  de los enteros se representa por int.

     Por ejemplo, la suma de 1 y -2 es el número entero -1. \<close>

value "(1::int) + -2"  \<comment> \<open>= -1\<close>
text \<open> Los numerales están sobrecargados. Por ejemplo, el 1 puede ser
  un natural o un entero, dependiendo del contexto.

  Isabelle resuelve ambigüedades mediante inferencia de tipos.

  A veces, es necesario usar declaraciones de tipo para resolver la
  ambigüedad.

  En Isabelle están definidos los valores booleanos (True y False), las
  conectivas (\<not>, \<and>, \<or>, \<longrightarrow> y \<longleftrightarrow>) y los cuantificadores (\<forall> y \<exists>).

  El tipo de los booleanos es bool. \<close>

text \<open> La conjunción de dos fórmulas verdaderas es verdadera. \<close>
value "True \<and> True"  \<comment> \<open>= True\<close>
text \<open> La conjunción de un fórmula verdadera y una falsa es falsa. \<close>
value "True \<and> False"  \<comment> \<open>= False\<close>
text \<open> La disyunción de una fórmula verdadera y una falsa es
  verdadera. \<close>
value "True \<or> False"  \<comment> \<open>= True\<close>
text \<open> La disyunción de dos fórmulas falsas es falsa. \<close>
value "False \<or> False"  \<comment> \<open>= False\<close>
text \<open> La negación de una fórmula verdadera es falsa. \<close>
value "\<not>True"  \<comment> \<open>= False\<close>
text \<open> Una fórmula falsa implica una fórmula verdadera. \<close>
value "False \<longrightarrow> True"  \<comment> \<open>= True\<close>
text \<open> Un lema introduce una proposición seguida de una demostración.

  Isabelle dispone de varios procedimientos automáticos para generar
  demostraciones, uno de los cuales es el de simplificación (llamado
  simp).

     El procedimiento simp aplica un conjunto de reglas de reescritura, que
     inicialmente contiene un gran número de reglas relativas a los objetos
     definidos. \<close>

text \<open> Ej. de simp: Todo elemento es igual a sí mismo. \<close>
lemma "\<forall>x. x = x"
by simp

text \<open> Ej. de simp: Existe un elemento igual a 1. \<close>
lemma "\<exists>x. x = 1"
by simp

section \<open> Definiciones no recursivas \<close>

text \<open> La disyunción exclusiva de A y B se verifica si una es verdadera
  y la otra no lo es. \<close>

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"

text \<open> Prop.: La disyunción exclusiva de dos fórmulas verdaderas es
  falsa.

     Dem.: Por simplificación, usando la definición de la disyunción
     exclusiva.
\<close>

lemma "xor True True = False"
by (simp add: xor_def)

text \<open> Se añade la definición de la disyunción exclusiva al conjunto de
  reglas de simplificación automáticas. \<close>

declare xor_def[simp]

lemma "xor True False = True"
by simp

section \<open> Definiciones locales \<close>

text \<open> Se puede asignar valores a variables locales mediante 'let' y
  usarlo en las expresiones dentro de 'in'.

  Por ejemplo, si x es el número natural 3, entonces "x*x=9". \<close>

value "let x = 3::nat in x * x"  \<comment> \<open>= 9\<close>
section \<open> Pares \<close>

text \<open> Un par se representa escribiendo los elementos entre paréntesis
  y separados por coma.

  El tipo de los pares es el producto de los tipos.

  La función fst devuelve el primer elemento de un par y la snd el
  segundo.

  Por ejemplo, si p es el par de números naturales (2,3), entonces la
  suma del primer elemento de p y 1 es igual al segundo elemento de
  p. \<close>

value "let p = (2,3)::nat \<times> nat in fst p + 1 = snd p"

section \<open> Listas \<close>

text \<open> Una lista se representa escribiendo los elementos entre
  corchetes y separados por comas.

  La lista vacía se representa por [].

  Todos los elementos de una lista tienen que ser del mismo tipo.

  El tipo de las listas de elementos del tipo a es (a list).

  El término (x#xs) representa la lista obtenida añadiendo el elemento x
  al principio de la lista xs.

  Por ejemplo, la lista obtenida añadiendo sucesivamente a la lista
  vacía los elementos c, b y a es [a,b,c]. \<close>

value "a#(b#(c#[]))"  \<comment> \<open>= [a,b,c]\<close>
text \<open> Funciones de descomposión de listas:
  \<sqdot> (hd xs) es el primer elemento de la lista xs.
  \<sqdot> (tl xs) es el resto de la lista xs.

     Por ejemplo, si xs es la lista [a,b,c], entonces el primero de xs es a
     y el resto de xs es [b,c]. \<close>

value "let xs = [a,b,c] in hd xs = a \<and> tl xs = [b,c]"  \<comment> \<open>= True\<close>
text \<open> (length xs) es la longitud de la lista xs. Por ejemplo, la
  longitud de la lista [1,2,3] es 3. \<close>

value "length [1,2,3::nat]"  \<comment> \<open>= 3\<close>
text \<open> En la sesión 47 de "Isabelle/HOL  Higher-Order Logic"
  http://goo.gl/sFsFF se encuentran más definiciones y propiedades de
  las listas. \<close>

section \<open> Registros \<close>

text \<open> Un registro es una colección de campos y valores.

     Por ejemplo, los puntos del plano se pueden representar mediante
     registros con dos campos, las coordenadas, con valores enteros. \<close>

record punto =
  coordenada_x :: int
  coordenada_y :: int

text \<open> Ejemplo, el punto pt tiene de coordenadas 3 y 7. \<close>

definition pt :: punto where
  "pt \<equiv> \<lparr>coordenada_x = 3, coordenada_y = 7\<rparr>"

text \<open> Ejemplo, la coordenada x del punto pt es 3. \<close>

value "coordenada_x pt"  \<comment> \<open>= 3\<close>
text \<open> Ejemplo, sea pt2 el punto obtenido a partir del punto pt
  cambiando el valor de su coordenada x por 4. Entonces la coordenada x
  del punto pt2 es 4. \<close>

value "let pt2 = pt\<lparr>coordenada_x:=4\<rparr> in coordenada_x (pt2)"  \<comment> \<open>= 4\<close>
section \<open> Funciones anónimas \<close>

text \<open> En Isabelle pueden definirse funciones anónimas.

  Por ejemplo, el valor de la función que a un número le asigna su doble
  aplicada a 1 es 2. \<close>

value "(\<lambda>x. x + x) 1::nat"  \<comment> \<open>= 2\<close>
section \<open> Condicionales \<close>

text \<open> El valor absoluto del entero x es x, si "x \<ge> 0" y es -x en caso
  contrario. \<close>

definition absoluto :: "int \<Rightarrow> int" where
  "absoluto x \<equiv> (if x \<ge> 0 then x else -x)"

text \<open> Ejemplo, el valor absoluto de -3 es 3. \<close>

value "absoluto(-3)"  \<comment> \<open>= 3\<close>
text \<open> Def.: Un número natural n es un sucesor si es de la forma
  (Suc m). \<close>

definition es_sucesor :: "nat \<Rightarrow> bool" where
  "es_sucesor n \<equiv> (case n of
    0     \<Rightarrow> False
  | Suc m \<Rightarrow> True)"

text \<open> Ejemplo, el número 3 es sucesor. \<close>

value "es_sucesor 3"  \<comment> \<open>= True\<close>
section \<open> Tipos de datos y definiciones recursivas \<close>

text \<open> Una lista de elementos de tipo a es la lista Vacia o se obtiene
  añadiendo, con Cons, un elemento de tipo a a una lista de elementos de
  tipo a. \<close>

datatype 'a Lista = Vacia | Cons 'a "'a Lista"

text \<open> (conc xs ys) es la concatenación de las lista xs e ys. Por
   ejemplo,
      conc (Cons a (Cons b Vacia)) (Cons c Vacia)
      = Cons a (Cons b (Cons c Vacia))
\<close>

fun conc :: "'a Lista \<Rightarrow> 'a Lista \<Rightarrow> 'a Lista" where
  "conc Vacia ys       = ys"
| "conc (Cons x xs) ys = Cons x (conc xs ys)"

value "conc (Cons a (Cons b Vacia)) (Cons c Vacia)"
text \<open>= Cons a (Cons b (Cons c Vacia))\<close>
text \<open> (suma n) es la suma de los primeros n números naturales. Por
   ejemplo,
      suma 3 = 6
\<close>

fun suma :: "nat \<Rightarrow> nat" where
  "suma 0       = 0"
| "suma (Suc m) = (Suc m) + suma m"

value "suma 3"  \<comment> \<open>= 6\<close>
text \<open> (sumaImpares n) es la suma de los n primeros números
   impares. Por ejemplo,
      sumaImpares 3 = 9
\<close>

fun sumaImpares :: "nat \<Rightarrow> nat" where
  "sumaImpares 0       = 0"
| "sumaImpares (Suc n) = (2 * (Suc n) - 1) + sumaImpares n"

value "sumaImpares 3"  \<comment> \<open>= 9\<close>
end
