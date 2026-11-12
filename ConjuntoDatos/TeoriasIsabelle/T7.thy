(* T7
   Tema 7 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T7
imports Main
begin

chapter \<open> Tema 7: Caso de estudio: Compilación de expresiones \<close>
text \<open>
   El objetivo de este tema es contruir un compilador de expresiones
   genéricas (construidas con variables, constantes y operaciones
   binarias) a una máquina de pila y demostrar su corrección.
\<close>

section \<open> Las expresiones y el intérprete \<close>

text \<open>
   Definición. Las expresiones son las constantes, las variables
   (representadas por números naturales) y las aplicaciones de operadores
   binarios a dos expresiones.
\<close>

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

datatype 'v expr =
  Const 'v
| Var nat

| App "'v binop" "'v expr" "'v expr"

text \<open>
   Definición. [Intérprete]
   La función "valor" toma como argumentos una expresión y un entorno
   (i.e. una aplicación de las variables en elementos del lenguaje) y
   devuelve el valor de la expresión en el entorno.
\<close>

fun valor :: "'v expr \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'v" where
  "valor (Const b) ent = b"
| "valor (Var x) ent = ent x"
| "valor (App f e1 e2) ent = (f (valor e1 ent) (valor e2 ent))"

text \<open>
   Ejemplo. A continuación mostramos algunos ejemplos de evaluación con
   el intérprete.
\<close>

lemma
  "valor (Const 3) id = 3 \<and>
   valor (Var 2) id = 2 \<and>
   valor (Var 2) (\<lambda>x. x+1) = 3 \<and>
   valor (App (+) (Const 3) (Var 2)) (\<lambda>x. x+1) = 6 \<and>
   valor (App (+) (Const 3) (Var 2)) (\<lambda>x. x+4) = 9"
by simp

section \<open> La máquina de pila \<close>

text \<open>
   Nota. La máquina de pila tiene tres clases de intrucciones:
   \<sqdot> cargar en la pila una constante,
   \<sqdot> cargar en la pila el contenido de una dirección y
   \<sqdot> aplicar un operador binario a los dos elementos superiores de la pila.
\<close>

datatype 'v instr =
  IConst 'v
| ILoad nat
| IApp "'v binop"

text \<open>
   Definición. [Ejecución]
   La ejecución de la máquina de pila se modeliza mediante la función
   "ejec" que toma una lista de intrucciones, una memoria (representada
   como una función de las direcciones a los valores, análogamente a los
   entornos) y una pila (representada como una lista) y devuelve la pila
   al final de la ejecución.
\<close>

fun ejec :: "'v instr list \<Rightarrow> (nat\<Rightarrow>'v) \<Rightarrow> 'v list \<Rightarrow> 'v list" where
  "ejec [] ent vs = vs"
| "ejec (i#is) ent vs =
     (case i of
        IConst v \<Rightarrow> ejec is ent (v#vs)
      | ILoad x \<Rightarrow> ejec is ent ((ent x)#vs)
      | IApp f \<Rightarrow> ejec is ent ((f (hd vs) (hd (tl vs)))#(tl(tl vs))))"

text \<open>
   A continuación se muestran ejemplos de ejecución.
\<close>

lemma
  "ejec [IConst 3] id [7] = [3,7] \<and>
   ejec [ILoad 2, IConst 3] id [7] = [3,2,7] \<and>
   ejec [ILoad 2, IConst 3] (\<lambda>x. x+4) [7] = [3,6,7] \<and>
   ejec [ILoad 2, IConst 3, IApp (+)] (\<lambda>x. x+4) [7] = [9,7]"
by simp

section \<open> El compilador \<close>

text \<open>
   Definición. El compilador "comp" traduce una expresión en una lista de
   instrucciones.
\<close>

fun comp :: "'v expr \<Rightarrow> 'v instr list" where
  "comp (Const v) = [IConst v]"
| "comp (Var x) = [ILoad x]"
| "comp (App f e1 e2) = (comp e2) @ (comp e1) @ [IApp f]"

text \<open>
   A continuación se muestran ejemplos de compilación.
\<close>

lemma
  "comp (Const 3) = [IConst 3] \<and>
   comp (Var 2) = [ILoad 2] \<and>
   comp (App (+) (Const 3) (Var 2)) = [ILoad 2, IConst 3, IApp (+)]"
by simp

section \<open> Corrección del compilador \<close>

text \<open>
   Para demostrar que el compilador es correcto, probamos que el
   resultado de compilar una expresión y a continuación ejecutarla es lo
   mismo que interpretarla; es decir,
\<close>

theorem "ejec (comp e) ent [] = [valor e ent]"
oops

text \<open>
   El teorema anterior no puede demostrarse por inducción en e. Para
   demostrarlo, lo generalizamos a
\<close>

theorem "\<forall>vs. ejec (comp e) ent vs = (valor e ent)#vs"
oops

text \<open>
   En la demostración del teorema anterior usaremos el siguiente lema.
\<close>

lemma ejec_append:
  "\<forall> vs. ejec (xs@ys) ent vs = ejec ys ent (ejec xs ent vs)" (is "?P xs")
proof (induct xs)
  show "?P []" by simp
next
  fix a xs

  assume "?P xs"
  thus "?P (a#xs)" by (cases "a", auto)
qed

text \<open>La demostración detallada es\<close>
lemma ejec_append_1:
  "\<forall> vs. ejec (xs@ys) ent vs = ejec ys ent (ejec xs ent vs)" (is "?P xs")
proof (induct xs)
  show "?P []" by simp
next
  fix a xs
  assume HI: "?P xs"
  thus "?P (a#xs)"
  proof (cases "a")
     case IConst thus ?thesis using HI by simp
  next
     case ILoad thus ?thesis using HI by simp
  next
     case IApp thus ?thesis using HI by simp
  qed
qed

text \<open>
   Una demostración más detallada del lema es la siguiente:
\<close>

lemma ejec_append_2:
  "\<forall>vs. ejec (xs@ys) ent vs = ejec ys ent (ejec xs ent vs)" (is "?P xs")
proof (induct xs)
  show "?P []" by simp
next
  fix a xs
  assume HI: "?P xs"
  thus "?P (a#xs)"
  proof (cases "a")
     fix v assume C1: "a=IConst v"
     show " \<forall>vs. ejec ((a#xs)@ys) ent vs = ejec ys ent (ejec (a#xs) ent vs)"
     proof
       fix vs
       have "ejec ((a#xs)@ys) ent vs = ejec (((IConst v)#xs)@ys) ent vs"

         using C1 by simp
       also have "... = ejec (xs@ys) ent (v#vs)" by simp
       also have "... = ejec ys ent (ejec xs ent (v#vs))" using HI by simp
       also have "... = ejec ys ent (ejec ((IConst v)#xs) ent vs)" by simp
       also have "... = ejec ys ent (ejec (a#xs) ent vs)" using C1 by simp
       finally show "ejec ((a#xs)@ys) ent vs =
                     ejec ys ent (ejec (a#xs) ent vs)" .
    qed
  next
    fix n assume C2: "a=ILoad n"
    show " \<forall>vs. ejec ((a#xs)@ys) ent vs = ejec ys ent (ejec (a#xs) ent vs)"
    proof
       fix vs
       have "ejec ((a#xs)@ys) ent vs = ejec (((ILoad n)#xs)@ys) ent vs"
         using C2 by simp
       also have "... = ejec (xs@ys) ent ((ent n)#vs)" by simp
       also have "... = ejec ys ent (ejec xs ent ((ent n)#vs))" using HI by simp
       also have "... = ejec ys ent (ejec ((ILoad n)#xs) ent vs)" by simp
       also have "... = ejec ys ent (ejec (a#xs) ent vs)" using C2 by simp
       finally show "ejec ((a#xs)@ys) ent vs =
                     ejec ys ent (ejec (a#xs) ent vs)" .
    qed
  next
    fix f assume C3: "a=IApp f"
    show "\<forall>vs. ejec ((a#xs)@ys) ent vs = ejec ys ent (ejec (a#xs) ent vs)"
    proof
       fix vs
       have "ejec ((a#xs)@ys) ent vs = ejec (((IApp f)#xs)@ys) ent vs"
         using C3 by simp
       also have "... = ejec (xs@ys) ent ((f (hd vs) (hd (tl vs)))#(tl(tl vs)))"
         by simp
       also have "... = ejec ys
                           ent
                           (ejec xs ent ((f (hd vs) (hd (tl vs)))#(tl(tl vs))))"
         using HI by simp
       also have "... = ejec ys ent (ejec ((IApp f)#xs) ent vs)" by simp
       also have "... = ejec ys ent (ejec (a#xs) ent vs)" using C3 by simp
       finally show "ejec ((a#xs)@ys) ent vs =
                     ejec ys ent (ejec (a#xs) ent vs)" .
    qed

  qed
qed

text \<open>
   La demostración automática del teorema es
\<close>

theorem "\<forall>vs. ejec (comp e) ent vs = (valor e ent)#vs"
by (induct e) (auto simp add:ejec_append)

text \<open>
   La demostración estructurada del teorema es
\<close>

theorem "\<forall>vs. ejec (comp e) ent vs = (valor e ent)#vs"
proof (induct e)
  fix v
  show "\<forall>vs. ejec (comp (Const v)) ent vs = (valor (Const v) ent)#vs" by simp
next
  fix x
  show "\<forall>vs. ejec (comp (Var x)) ent vs = (valor (Var x) ent) # vs" by simp
next
  fix f e1 e2
  assume HI1: "\<forall>vs. ejec (comp e1) ent vs = (valor e1 ent) # vs"
     and HI2: "\<forall>vs. ejec (comp e2) ent vs = (valor e2 ent) # vs"
  show "\<forall>vs. ejec (comp (App f e1 e2)) ent vs = (valor (App f e1 e2) ent) # vs"
  proof
     fix vs
     have "ejec (comp (App f e1 e2)) ent vs
            = ejec ((comp e2) @ (comp e1) @ [IApp f]) ent vs" by simp
     also have "... = ejec ((comp e1) @ [IApp f]) ent (ejec (comp e2) ent vs)"
       using ejec_append by blast
     also have "... = ejec [IApp f]
                           ent
                           (ejec (comp e1) ent (ejec (comp e2) ent vs))"
       using ejec_append by blast
     also have "... = ejec [IApp f] ent (ejec (comp e1) ent ((valor e2 ent)#vs))"
       using HI2 by simp
     also have "... = ejec [IApp f] ent ((valor e1 ent)#((valor e2 ent)#vs))"
       using HI1 by simp

    also have "... = (f (valor e1 ent) (valor e2 ent))#vs" by simp
    also have "... = (valor (App f e1 e2) ent) # vs" by simp
    finally
    show "ejec (comp (App f e1 e2)) ent vs = (valor (App f e1 e2) ent) # vs"
      by blast
  qed
qed

end
