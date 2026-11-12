theory EjemplosTipoListas
  imports Main

begin
text\<open>
                           El tipo de datos lista 
\<close>

text\<open>
     El tipo de datos lista introduce dos constructores Nil y Cons:
     La lista vacia y el operador que adiciona un elemento al frente de la lista. 
\<close>

text\<open>
   datatype 'a list = Nil  ("[]")
             | Cons 'a " 'a list" (infixr "#" 65)
\<close>

value "Cons (3::nat) Nil" 
value "((3::nat) # Nil)"

lemma  "Cons (3::nat) Nil == ((3::nat) # Nil)" .

lemma  "Cons (3::nat) Nil == [3]".

lemma  "2 # Cons 3 Nil == [2,3]" . 

lemma  "1# 2 # 3 # Nil == [1, 2, 3]".

text\<open>
\<close>

text\<open>   Concatenación de listas:

En la teoría de listas de Isabelle, la concatenación de dos listas se define por: 

primrec append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr \<open>@\<close> 65) where
append_Nil: "[] @ ys = ys" |
append_Cons: "(x#xs) @ ys = x # xs @ ys

\<close>

(* Inversa de una lista: *)

fun inversa :: "'a list \<Rightarrow> 'a list" where
"inversa [] = []"
| "inversa (x#xs) = inversa xs @ [x]"


text\<open>
    En la teoría de listas de Isabelle, la inversa se define por: 

primrec rev :: "'a list => 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ (x # [])"
\<close> 

text\<open> La inversa de una lista unitaria es la misma lista
\<close>
(* Demostración detallada: *)

lemma "inversa [x] = [x]"
proof -
  have "inversa [x] = inversa (x#[])" by simp
  also have "... = (inversa []) @ [x]" by (simp only: inversa.simps(2))
  also have "... = [] @ [x]" by (simp only: inversa.simps(1))
  also have "... = [x]" by (simp only: append_Nil)
  finally show "inversa [x] = [x]" by simp
qed

(* Demostración estructurada: *)
lemma "inversa [x] = [x]"
proof -
  have "inversa [x] = inversa (x#[])" by simp
  also have "... = (inversa []) @ [x]" by simp
  also have "... = [] @ [x]" by simp
  also have "... = [x]" by simp
  finally show "inversa [x] = [x]" by simp
qed

(* Demostración automática: *)
lemma "inversa [x] = [x]"
  by simp

text\<open>  Razonamiento por inducción  sobre listas \<close>

thm list.induct
text\<open> esquema de inducción list.induct:

                             \<lbrakk> P [];
                               \<And>x1 x2. P x2 \<Longrightarrow> P (x1 # x2)\<rbrakk>
                             \<Longrightarrow> P list
\<close>

text\<open>
 funcion  Concatencaión de listas
\<close>

fun conc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"conc [] ys = ys"
| "conc (x#xs) ys = x # (conc xs ys)"

text\<open>
 La concatenaciones asociativa: \<close>

(* Demostración estructurada: *)
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
proof (induct xs)
  show "conc [] (conc ys zs) = conc (conc [] ys) zs" by simp
next
  fix x xs
  assume HI: "conc xs (conc ys zs) = conc (conc xs ys) zs"
  have "conc (x # xs) (conc ys zs) = x # (conc xs (conc ys zs))" by simp
  also have "... = x # (conc (conc xs ys) zs)" using HI by simp
  also have "... = conc (x # (conc xs ys)) zs" by simp
  also have "... = conc (conc (x # xs) ys) zs" by simp
  finally show "conc (x # xs) (conc ys zs) = conc (conc (x # xs) ys) zs" by simp
qed

(* Demostración por casos de inducción: *)
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
proof (induct xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case
  proof-
    have "conc (x # xs) (conc ys zs) = x # (conc xs (conc ys zs))" by simp
    also have "... = x # (conc (conc xs ys) zs)" by (simp add: local.Cons)
    also have "... = conc (x # (conc xs ys)) zs" by simp
    also have "... = conc (conc (x # xs) ys) zs" by simp
    finally show "conc (x # xs) (conc ys zs) = conc (conc (x # xs) ys) zs" by simp
  qed
qed

(* Demostración automática: *)
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
  by (induct xs) auto

text\<open>La concatencación no es conmutativa\<close>  
lemma "conc xs ys = conc ys xs"
quickcheck
  oops

text\<open>La lista vacía es el elemento identidad  de la concatenación\<close> 
(* La demostración estructurada es: *)

lemma "conc xs [] = xs"
proof (induct xs)
  show "conc [] [] = []" by simp
next
  fix x xs
  assume HI: "conc xs [] = xs"
  have "conc (x # xs) [] = x # (conc xs [])" by simp
  also have "... = x # xs" using HI by simp
  finally show "conc (x # xs) [] = x # xs" by simp
qed

(* La demostración automática es: *)
lemma "conc xs [] = xs"
  by (induct xs) auto

text\<open> Definición de la longitud de una lista:\<close>

fun longitud :: "'a list \<Rightarrow> nat" where
"longitud [] = 0"
| "longitud (x#xs) = 1 + longitud xs"

text\<open> La longitud de la concatenacioón de dos listas es la suma de las longitudes de las listas\<close>

(* Demostración estrucuturada: *)
lemma "longitud (conc xs ys) = longitud xs + longitud ys"
proof (induct xs)
  show "longitud (conc [] ys) = longitud [] + longitud ys" by simp
next
  fix x xs
  assume HI: "longitud (conc xs ys) = longitud xs + longitud ys"
  have "longitud (conc (x # xs) ys) = longitud (x # (conc xs ys))"
    by simp
  also have "... = 1 + longitud (conc xs ys)" by simp
  also have "... = 1 + longitud xs + longitud ys" using HI by simp
  also have "... = longitud (x # xs) + longitud ys" by simp
  finally show "longitud (conc (x # xs) ys) = longitud (x # xs) + longitud ys" 
    by simp
qed

(* Demostración automática: *)
lemma "longitud (conc xs ys) = longitud xs + longitud ys"
by (induct xs) auto

                 (* Ejercicios: *)
lemma inv_conc [simp]: "inversa(xs @ ys) = (inversa ys) @ (inversa xs)" 
  oops 

theorem inv_inv [simp]: "inversa (inversa xs) = xs"  
  oops 

end
text\<open> 
\<close>