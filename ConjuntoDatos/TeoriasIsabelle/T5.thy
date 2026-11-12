(* T5
   Tema 5 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T5
imports Main
begin

chapter \<open> Tema 5: Razonamiento sobre programas \<close>
text \<open>
  En este tema se demuestra con Isabelle las propiedades de los
  programas funcionales como se expone en el tema 8 del curso
  "Informática" que puede leerse en http://goo.gl/Imvyt \<close>

section \<open> Razonamiento ecuacional \<close>

text \<open> ----------------------------------------------------------------
  Ejemplo 1. Definir, por recursión, la función
     longitud :: 'a list \<Rightarrow> nat
  tal que (longitud xs) es la longitud de la lista xs. Por ejemplo,
     longitud [4,2,5] = 3
  ------------------------------------------------------------------- \<close>

fun longitud :: "'a list \<Rightarrow> nat" where
  "longitud []     = 0"
| "longitud (x#xs) = 1 + longitud xs"

value "longitud [4,2,5::nat]"  \<comment> \<open>= 3\<close>
text \<open> ---------------------------------------------------------------

     Ejemplo 2. Demostrar que
        longitud [4,2,5] = 3
     ------------------------------------------------------------------- \<close>

lemma "longitud [4,2,5] = 3"
by simp

text \<open> ---------------------------------------------------------------
  Ejemplo 3. Definir la función
     fun intercambia :: 'a \<times> 'b \<Rightarrow> 'b \<times> 'a
  tal que (intercambia p) es el par obtenido intercambiando las
  componentes del par p. Por ejemplo,
     intercambia (u,v) = (v,u)
  ------------------------------------------------------------------ \<close>

fun intercambia :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a" where
  "intercambia (x,y) = (y,x)"

value "intercambia (u,v)"  \<comment> \<open>= (v,u)\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 4. (p.6) Demostrar que
     intercambia (intercambia (x,y)) = (x,y)
  ------------------------------------------------------------------- \<close>

text \<open>La demostración detallada es\<close>
lemma "intercambia (intercambia (x,y)) = (x,y)"
proof -
  have "intercambia (intercambia (x,y)) = intercambia (y,x)"
    by (simp only: intercambia.simps)
  also have "... = (x,y)"
    by (simp only: intercambia.simps)
  finally show "intercambia (intercambia (x,y)) = (x,y)" by simp
qed

text \<open>
  El razonamiento ecuacional se realiza usando la combinación de "also"
  (además) y "finally" (finalmente). \<close>

text \<open>La demostración estructurada es\<close>
lemma "intercambia (intercambia (x,y)) = (x,y)"
proof -
  have "intercambia (intercambia (x,y)) = intercambia (y,x)" by simp
  also have "... = (x,y)" by simp
  finally show "intercambia (intercambia (x,y)) = (x,y)" by simp
qed

text \<open>La demostración automática es\<close>
lemma "intercambia (intercambia (x,y)) = (x,y)"
by simp

text \<open> ---------------------------------------------------------------
  Ejemplo 5. Definir, por recursión, la función
     inversa :: 'a list \<Rightarrow> 'a list
  tal que (inversa xs) es la lista obtenida invirtiendo el orden de los
  elementos de xs. Por ejemplo,
     inversa [a,d,c] = [c,d,a]
  ------------------------------------------------------------------ \<close>

fun inversa :: "'a list \<Rightarrow> 'a list" where
  "inversa []     = []"
| "inversa (x#xs) = inversa xs @ [x]"

value "inversa [a,d,c]"  \<comment> \<open>= [c,d,a]\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 6. (p. 9) Demostrar que
     inversa [x] = [x]
  ------------------------------------------------------------------- \<close>

text \<open>La demostración detallada es\<close>
lemma "inversa [x] = [x]"
proof -
  have "inversa [x] = inversa (x#[])" by simp
  also have "... = (inversa []) @ [x]" by (simp only: inversa.simps(2))
  also have "... = [] @ [x]" by (simp only: inversa.simps(1))
  also have "... = [x]" by (simp only: append_Nil)
  finally show "inversa [x] = [x]" by simp
qed

text \<open>La demostración estructurada es\<close>
lemma "inversa [x] = [x]"
proof -
  have "inversa [x] = inversa (x#[])" by simp
  also have "... = (inversa []) @ [x]" by simp
  also have "... = [] @ [x]" by simp
  also have "... = [x]" by simp
  finally show "inversa [x] = [x]" by simp
qed

text \<open>La demostración automática es\<close>
lemma "inversa [x] = [x]"
by simp

section \<open> Razonamiento por inducción sobre los naturales \<close>

text \<open>
  [Principio de inducción sobre los naturales] Para demostrar una
  propiedad P para todos los números naturales basta probar que el 0
  tiene la propiedad P y que si n tiene la propiedad P, entonces n+1
  también la tiene.
     \<lbrakk>P 0;\<And>n. P n \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P m

     En Isabelle el principio de inducción sobre los naturales está
     formalizado en el teorema nat.induct y puede verse con
        thm nat.induct
\<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 7. Definir la función
     repite :: nat \<Rightarrow> 'a \<Rightarrow> 'a list
  tal que (repite n x) es la lista formada por n copias del elemento
  x. Por ejemplo,
     repite 3 a = [a,a,a]
  ------------------------------------------------------------------ \<close>

fun repite :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "repite 0 x       = []"
| "repite (Suc n) x = x # (repite n x)"

value "repite 3 a"  \<comment> \<open>= [a,a,a]\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 8. (p. 18) Demostrar que
     longitud (repite n x) = n
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
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

text \<open>La demostración automática es\<close>
lemma "longitud (repite n x) = n"
by (induct n) auto

section \<open> Razonamiento por inducción sobre listas \<close>

text \<open>
  Para demostrar una propiedad para todas las listas basta demostrar
  que la lista vacía tiene la propiedad y que al añadir un elemento a una
  lista que tiene la propiedad se obtiene otra lista que también tiene la
  propiedad.

     En Isabelle el principio de inducción sobre listas está formalizado
     mediante el teorema list.induct que puede verse con
        thm list.induct
\<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 9. Definir la función

        conc :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list
     tal que (conc xs ys) es la concatención de las listas xs e ys. Por
     ejemplo,
        conc [a,d] [b,d,a,c] = [a,d,b,d,a,c]
     ------------------------------------------------------------------ \<close>

fun conc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "conc []     ys = ys"
| "conc (x#xs) ys = x # (conc xs ys)"

value "conc [a,d] [b,d,a,c]"  \<comment> \<open>= [a,d,b,d,a,c]\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 10. (p. 24) Demostrar que
     conc xs (conc ys zs) = (conc xs ys) zs
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
proof (induct xs)
  show "conc [] (conc ys zs) = conc (conc [] ys) zs" by simp
next
  fix x xs
  assume HI: "conc xs (conc ys zs) = conc (conc xs ys) zs"
  have "conc (x # xs) (conc ys zs) = x # (conc xs (conc ys zs))" by simp
  also have "... = x # (conc (conc xs ys) zs)" using HI by simp
  also have "... = conc (conc (x # xs) ys) zs" by simp
  finally show "conc (x # xs) (conc ys zs) = conc (conc (x # xs) ys) zs" by simp
qed

text \<open>La demostración automática es\<close>
lemma "conc xs (conc ys zs) = conc (conc xs ys) zs"
by (induct xs) auto

text \<open> ---------------------------------------------------------------
  Ejemplo 11. Refutar que
     conc xs ys = conc ys xs
  ------------------------------------------------------------------- \<close>

lemma "conc xs ys = conc ys xs"

quickcheck
oops

text \<open> Encuentra el contraejemplo,
  xs = [a2]
  ys = [a1] \<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 12. (p. 28) Demostrar que
     conc xs [] = xs
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
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

text \<open>La demostración automática es\<close>
lemma "conc xs [] = xs"
by (induct xs) auto

text \<open> ---------------------------------------------------------------
  Ejemplo 13. (p. 30) Demostrar que
     longitud (conc xs ys) = longitud xs + longitud ys
  ------------------------------------------------------------------- \<close>

text \<open>La demostración automática es\<close>
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
  finally show "longitud (conc (x # xs) ys) =
                longitud (x # xs) + longitud ys" by simp
qed

text \<open>La demostración automática es\<close>
lemma "longitud (conc xs ys) = longitud xs + longitud ys"
by (induct xs) auto

section \<open> Inducción correspondiente a la definición recursiva \<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 14. Definir la función
     coge :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list
  tal que (coge n xs) es la lista de los n primeros elementos de xs. Por
  ejemplo,
     coge 2 [a,c,d,b,e] = [a,c]
  ------------------------------------------------------------------ \<close>

fun coge :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "coge n []           = []"
| "coge 0 xs           = []"
| "coge (Suc n) (x#xs) = x # (coge n xs)"

value "coge 2 [a,c,d,b,e]"  \<comment> \<open>= [a,c]\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 15. Definir la función
     elimina :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list
  tal que (elimina n xs) es la lista obtenida eliminando los n primeros
  elementos de xs. Por ejemplo,
     elimina 2 [a,c,d,b,e] = [d,b,e]
  ------------------------------------------------------------------ \<close>

fun elimina :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "elimina n []          = []"

| "elimina 0 xs           = xs"
| "elimina (Suc n) (x#xs) = elimina n xs"

value "elimina 2 [a,c,d,b,e]"  \<comment> \<open>= [d,b,e]\<close>
text \<open>
  La definición coge genera el esquema de inducción coge.induct:
     \<lbrakk>\<And>n. P n [];

       \<And> x xs. P 0 (x#xs);

       \<And> n x xs. P n xs \<Longrightarrow> P (Suc n) (x#xs)\<rbrakk>

     \<Longrightarrow> P n x

  Puede verse usando "thm coge.induct". \<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 16. (p. 35) Demostrar que
     conc (coge n xs) (elimina n xs) = xs
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
lemma "conc (coge n xs) (elimina n xs) = xs"
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
  finally show "conc (coge (Suc n) (x#xs)) (elimina (Suc n) (x#xs)) = x#xs"
     by simp
qed

text \<open>La demostración automática es\<close>
lemma "conc (coge n xs) (elimina n xs) = xs"

by (induct rule: coge.induct) auto

section \<open> Razonamiento por casos \<close>

text \<open>
  Distinción de casos sobre listas:
  \<sqdot> El método de distinción de casos se activa con (cases xs) donde xs
    es del tipo lista.
  \<sqdot> "case Nil" es una abreviatura de
        "assume Nil: xs =[]".
  \<sqdot> "case Cons" es una abreviatura de
        "fix ? ?? assume Cons: xs = ? # ??"
    donde ? y ?? son variables anónimas. \<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 17. Definir la función
     esVacia :: 'a list \<Rightarrow> bool
  tal que (esVacia xs) se verifica si xs es la lista vacía. Por ejemplo,
     esVacia [] = True
     esVacia [1] = False
  ------------------------------------------------------------------ \<close>

fun esVacia :: "'a list \<Rightarrow> bool" where
  "esVacia []     = True"
| "esVacia (x#xs) = False"

value "esVacia ([]::nat list)"  \<comment> \<open>= True\<close>
value "esVacia [1::nat]"  \<comment> \<open>= False\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 18 (p. 39) . Demostrar que
     esVacia xs = esVacia (conc xs xs)
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
lemma "esVacia xs = esVacia (conc xs xs)"
proof (cases xs)
  assume "xs = []"
  thus "esVacia xs = esVacia (conc xs xs)" by simp
next

  fix y ys
  assume "xs = y#ys"
  thus "esVacia xs = esVacia (conc xs xs)" by simp
qed

text \<open>La demostración estructurada simplificada es\<close>
lemma "esVacia xs = esVacia (conc xs xs)"
proof (cases xs)
  case Nil
  thus "esVacia xs = esVacia (conc xs xs)" by simp
next
  case Cons
  thus "esVacia xs = esVacia (conc xs xs)" by simp
qed

text \<open>La demostración automática es\<close>
lemma "esVacia xs = esVacia (conc xs xs)"
by (cases xs) auto

section \<open> Heurística de generalización \<close>

text \<open>
  Heurística de generalización: Cuando se use demostración estructural,
  cuantificar universalmente las variables libres (o, equivalentemente,
  considerar las variables libres como variables arbitrarias). \<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 19. Definir la función
     inversaAc :: 'a list \<Rightarrow> 'a list
  tal que (inversaAc xs) es a inversa de xs calculada usando
  acumuladores. Por ejemplo,
     inversaAc [a,c,b,e] = [e,b,c,a]
  ------------------------------------------------------------------ \<close>

fun inversaAcAux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inversaAcAux [] ys     = ys"
| "inversaAcAux (x#xs) ys = inversaAcAux xs (x#ys)"

fun inversaAc :: "'a list \<Rightarrow> 'a list" where
  "inversaAc xs = inversaAcAux xs []"

value "inversaAc [a,c,b,e]"  \<comment> \<open>= [e,b,c,a]\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 20. (p. 44) Demostrar que
     inversaAcAux xs ys = (inversa xs) @ ys
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
lemma inversaAcAux_es_inversa:
  "inversaAcAux xs ys = (inversa xs) @ ys"
proof (induct xs arbitrary: ys)
  show "\<And>ys. inversaAcAux [] ys = inversa [] @ ys" by simp

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

text \<open>La demostración automática es\<close>
lemma "inversaAcAux xs ys = (inversa xs)@ys"
by (induct xs arbitrary: ys) auto

text \<open> ---------------------------------------------------------------
  Ejemplo 21. (p. 43) Demostrar que
     inversaAc xs = inversa xs
  ------------------------------------------------------------------- \<close>

text \<open>La demostración automática es\<close>
corollary "inversaAc xs = inversa xs"
by (simp add: inversaAcAux_es_inversa)

section \<open> Demostración por inducción para funciones de orden superior \<close>

text \<open> ---------------------------------------------------------------
  Ejemplo 22. Definir la función
     sum :: nat list \<Rightarrow> nat
  tal que (sum xs) es la suma de los elementos de xs. Por ejemplo,
     sum [3,2,5] = 10
  ------------------------------------------------------------------ \<close>

fun sum :: "nat list \<Rightarrow> nat" where
  "sum []     = 0"
| "sum (x#xs) = x + sum xs"

value "sum [3,2,5]"  \<comment> \<open>= 10\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 23. Definir la función
     map :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list
  tal que (map f xs) es la lista obtenida aplicando la función f a los
  elementos de xs. Por ejemplo,
     map (\<lambda>x. 2*x) [3,2,5] = [6,4,10]
  ------------------------------------------------------------------ \<close>

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map f []     = []"
| "map f (x#xs) = (f x) # map f xs"

value "map (\<lambda>x. 2*x) [3::nat,2,5]"  \<comment> \<open>= [6,4,10]\<close>
text \<open> ---------------------------------------------------------------
  Ejemplo 24. (p. 45) Demostrar que
     sum (map (\<lambda>x. 2*x) xs) = 2 * (sum xs)
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
lemma "sum (map (\<lambda>x. 2*x) xs) = 2 * (sum xs)"
proof (induct xs)
  show "sum (map (\<lambda>x. 2*x) []) = 2 * (sum [])" by simp
next
  fix a xs
  assume HI: "sum (map (\<lambda>x. 2*x) xs) = 2 * (sum xs)"

  have "sum (map (\<lambda>x. 2*x) (a#xs)) = sum ((2*a)#(map (\<lambda>x. 2*x) xs))"
    by simp
  also have "... = 2*a + sum (map (\<lambda>x. 2*x) xs)" by simp
  also have "... = 2*a + 2*(sum xs)" using HI by simp
  also have "... = 2*(a + sum xs)" by simp
  also have "... = 2*(sum (a#xs))" by simp
  finally show "sum (map (\<lambda>x. 2*x) (a#xs)) = 2*(sum (a#xs))" by simp
qed

text \<open>La demostración automática es\<close>
lemma "sum (map (\<lambda>x. 2*x) xs) = 2 * (sum xs)"
by (induct xs) auto

text \<open> ---------------------------------------------------------------
  Ejemplo 25. (p. 48) Demostrar que
     longitud (map f xs) = longitud xs
  ------------------------------------------------------------------- \<close>

text \<open>La demostración estructurada es\<close>
lemma "longitud (map f xs) = longitud xs"
proof (induct xs)
  show "longitud (map f []) = longitud []" by simp
next
  fix a xs
  assume HI: "longitud (map f xs) = longitud xs"
  have "longitud (map f (a#xs)) = longitud (f a # (map f xs))" by simp
  also have "... = 1 + longitud (map f xs)" by simp
  also have "... = 1 + longitud xs" using HI by simp
  also have "... = longitud (a#xs)" by simp
  finally show "longitud (map f (a#xs)) = longitud (a#xs)" by simp
qed

text \<open>La demostración automática es\<close>
lemma "longitud (map f xs) = longitud xs"
by (induct xs) auto

section \<open> Referencias \<close>

text \<open>
  \<sqdot> J.A. Alonso. "Razonamiento sobre programas" http://goo.gl/R06O3

     \<sqdot> G. Hutton. "Programming in Haskell". Cap. 13 "Reasoning about
       programms".
     \<sqdot> S. Thompson. "Haskell: the Craft of Functional Programming, 3rd
       Edition. Cap. 8 "Reasoning about programms".
     \<sqdot> L. Paulson. "ML for the Working Programmer, 2nd Edition". Cap. 6.
       "Reasoning about functional programs".
\<close>

end
