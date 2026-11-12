theory OtrosEjemplosListas
  imports Main

begin
text\<open>
   datatype 'a list = Nil  ("[]")
             | Cons 'a " 'a list" (infixr "#" 65) ---> Cons x xs se denota x # xs

Una lista es:
- la lista vacía: []
- O es de la forma: x # xs donde x es un elemento de tipo 'a y xs es una lista.
\<close>

fun longitud :: "'a list \<Rightarrow> nat" where
"longitud [] = 0"
| "longitud (x#xs) = 1 + longitud xs" 

text\<open> La siguiente función construye una lista con la repetición de n-veces el elemento x 
\<close>

primrec repite :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"repite 0 x = []"
| "repite (Suc n) x = x # (repite n x)"

lemma "longitud (repite n x) = n"
proof (induct n)
  show "longitud (repite 0 x) = 0" by simp
next
  fix n
  assume HI: "longitud (repite n x) = n"
  have "longitud (repite (Suc n) x) = longitud (x # (repite n x))"
    by simp
  also have "... = 1 + longitud (repite n x)" by simp 
  also have "... = 1 + n" using HI by simp
  finally show "longitud (repite (Suc n) x) = Suc n" by simp
qed

lemma "longitud (repite n x) = n"
  by (induct n) auto

text
\<open> La siguiente función devuelve una lista con los primeros n elementos de una lista dada
\<close>

fun coge :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"coge n [] = []"
| "coge 0 xs = []"
| "coge (Suc n) (x#xs) = x # (coge n xs)"

text\<open> Esquema de inducción de la función coge: \<close>

thm coge.induct

text\<open>
                                  \<lbrakk>\<And>n. P n [];
                                   \<And>x xs. P 0 (x#xs); 
                                   \<And>n x xs. P n xs \<Longrightarrow> P (Suc n) (x#xs)\<rbrakk>
                                  \<Longrightarrow> P n l
\<close>
text\<open> La siguiente función devuelve una lista eliminando los primeros n elementos de una lista dada
\<close>

fun elimina :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"elimina n [] = []"
| "elimina 0 xs = xs"
| "elimina (Suc n) (x#xs) = elimina n xs"

value "elimina 2 [2::nat,3,2,2]"
thm elimina.induct

text\<open>                              Definción por casos
\<close>

fun elimina1 :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
elimina1_Nil: "elimina1 n [] = []" |
elimina1_Cons: "elimina1 n (x#xs) = (case n of
                                     0 => x#xs |
                                     Suc(m) => elimina1 m xs)"
thm elimina1.induct

fun conc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"conc [] ys = ys"
| "conc (x#xs) ys = x # (conc xs ys)"

lemma  "conc (coge n xs) (elimina n xs) = xs"
proof (induct rule: coge.induct)
  fix n
  show "conc (coge n []) (elimina n []) = []" by simp
next
  fix x xs
  show "conc (coge 0 (x#xs)) (elimina 0 (x#xs)) = x#xs" by simp
next
  fix n x xs
  assume HI: "conc (coge n xs) (elimina n xs) = xs"
  have "conc (coge (Suc n) (x#xs)) (elimina (Suc n) (x#xs)) =
        conc (x#(coge n xs)) (elimina n xs)" by simp
  also have "... = x#(conc (coge n xs) (elimina n xs))" by simp
  also have "... = x#xs" using HI by simp
  finally 
  show "conc (coge (Suc n) (x#xs)) (elimina (Suc n) (x#xs)) = x#xs"
    by simp
qed

lemma "conc (coge n xs) (elimina n xs) = xs"
by (induct rule: coge.induct) auto

text\<open> 
                              Cuantificación sobre listas
\<close> 

text\<open> 
La siguiente función verifica si todos los elementos de una lista verifican la propieda p                             
\<close> 
fun todos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"todos p [] = True"
| "todos p (y#ys) = ((p y) \<and> (todos p ys))"

lemma "(todos  (\<lambda>x. 0 <  x)[2::nat,-1,4]) = True" by auto

lemma "todos  (\<lambda>x. 1 < (longitud x))[[3],[2]] = True" by simp  

text\<open> El predicado todos distribuye sobre la  \<and>
\<close>

text\<open> 
 La demostración detallada es:
\<close>

lemma "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
proof (induct xs)
  show "todos (\<lambda>x. P x \<and> Q x) [] = (todos P [] \<and> todos Q [])" by simp
next
  fix a xs
  assume HI: "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
  show "todos (\<lambda>x. P x \<and> Q x) (a#xs) = (todos P (a#xs) \<and> todos Q (a#xs))"
  proof-
    have "todos (\<lambda>x. P x \<and> Q x) (a#xs) =
         ((P a) \<and> (Q a) \<and> todos (\<lambda>x. P x \<and> Q x) xs)" by simp
    also have "\<dots> = ((P a) \<and> (Q a) \<and> todos P xs \<and> todos Q xs)" using HI by simp
    also have "\<dots> = (((P a) \<and> todos P xs) \<and> ((Q a) \<and> todos Q xs))" by auto
    also have "\<dots> = (todos P (a#xs) \<and> todos Q (a#xs))" by simp
    finally show ?thesis.
  qed
qed
text\<open> 
 La demostración estructurada es:
\<close>

lemma "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
proof (induct xs)
  show "todos (\<lambda>x. P x \<and> Q x) [] = (todos P [] \<and> todos Q [])" by simp
next
  fix a xs
  assume "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
  thus "todos (\<lambda>x. P x \<and> Q x) (a#xs) = (todos P (a#xs) \<and> todos Q (a#xs))"
    by auto
qed

text\<open> 
La demostración automática es:
\<close>
lemma "todos (\<lambda>x. P x \<and> Q x) xs = (todos P xs \<and> todos Q xs)"
  by (induct xs) auto

text\<open> 
Ejercicio: definir una función que verifique que algún elemento cumple la propiedad P
\<close>
end
text\<open> 
\<close>