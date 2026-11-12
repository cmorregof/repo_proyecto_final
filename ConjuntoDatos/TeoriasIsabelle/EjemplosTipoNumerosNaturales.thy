theory EjemplosTipoNumerosNaturales
  imports Main

begin

text\<open>     El tipo Números naturales  \<close>

text\<open>  
     datatype  nat =  zero  ("0") | Suc nat
 \<close>

lemma "(Suc (Suc 0)) == 2"  by linarith  

text\<open>     Razonamiento por inducción  sobre los números naturales \<close>

thm nat.induct

text\<open> esquema de inducción nat.induct:

                             \<lbrakk> P 0;
                               \<And>n. P n \<Longrightarrow> P (Suc n)\<rbrakk>
                             \<Longrightarrow> P n
\<close>
text\<open>     Ejemplo de definicion del tipo  números naturales \<close>

fun par_nesimo:: "nat \<Rightarrow> nat" where
"par_nesimo 0 = 0"
| "par_nesimo (Suc n) = 2*(n+1)"

fun Suma_pares:: "nat \<Rightarrow> nat" where
  "Suma_pares 0 = 0" 
| "Suma_pares (Suc n) = (Suma_pares  n) + 2*(n+1)"

value "Suma_pares 3 "

lemma suma_pares: "Suma_pares n = n*(n+1)"
proof (induct n)
  case 0
  have "(Suma_pares 0) = 0 * (0 + 1)" by simp
  then show ?case by simp
next
  case (Suc n)
  fix n
  assume HI: "Suma_pares n = n * (n + 1)"
  show  "Suma_pares (Suc n) = Suc n * (Suc n + 1)" 
  proof-
    have  "Suma_pares (Suc n) = (Suma_pares  n) + 2*(n+1)" by simp
    also
    have  "... =  (Suma_pares  n) + 2*n + 2" by simp
    also 
    have "... =  n* (n+1) + 2*n + 2" using  HI  by simp
    also 
    have "... =  n* (n+1) + 2*(n + 1)" by simp
    also 
    have "... =   (n+2) * (n+1)" by simp
    finally show ?thesis by simp
  qed
qed

fun Suma_impares:: "nat \<Rightarrow> nat" where
  "Suma_impares 0 = 0" 
| "Suma_impares (Suc n) = (Suma_impares  n) + 2*n+1"

lemma suma_impares:"Suma_impares n = n*n" 
proof (induct n)
  show "Suma_impares 0 = 0 * 0" by simp
next
  fix n
  assume "Suma_impares n = n * n"
  show "Suma_impares (Suc n) = Suc n * Suc n"
    by (simp add: \<open>Suma_impares n = n * n\<close>)
qed

text\<open>
                          El n-ésimo número impar

En HOL toda función es total: no se puede dejar sin definir en 0. Se le da
un valor por convenio. Con 0 coincide con la fórmula 2*n - 1, porque en
los naturales la resta se trunca: 2*0 - 1 = 0.
\<close>

fun impar_nesimo:: "nat \<Rightarrow> nat" where
"impar_nesimo 0 = 0"
| "impar_nesimo (Suc n) = 2*(n+1)-1"

value "impar_nesimo 3"

lemma impar_nesimo_formula: "impar_nesimo n = 2*n - 1"
  by (cases n) auto

text\<open>
El valor en 0 es para completar la definición: 0 no es impar. Por eso la condición 0 < n
va en el enunciado del siguiente lema, no en la definición de la función.
\<close>

lemma impar_nesimo_es_impar: "0 < n \<Longrightarrow> odd (impar_nesimo n)"
  by (cases n) auto

lemma "\<not> odd (impar_nesimo 0)" by simp

text\<open>
Suma_impares suma justamente los n primeros impares: cada paso añade el
siguiente. El valor de impar_n-ésimo en 0 no interviene.
\<close>

lemma Suma_impares_paso:
  "Suma_impares (Suc n) = Suma_impares n + impar_nesimo (Suc n)"
  by simp

text\<open>
Junto con el lema suma_impares: la suma de los n primeros impares es n*n.
\<close>

fun Suma_naturales:: "nat \<Rightarrow> nat" where
  "Suma_naturales 0 = 0" 
| "Suma_naturales(Suc n) = (Suma_naturales  n) + n+1"

lemma suma_naturales: "2*(Suma_naturales n) = n*(n+1)"  by (induct n) auto 

lemma shows "Suma_naturales (2*n) = Suma_pares n + (Suma_impares  n)"
proof-
  have "2*Suma_naturales (2*n) = 2*(Suma_pares n + (Suma_impares  n))"
  using suma_pares suma_impares suma_naturales
  by simp
  thus ?thesis by simp
qed

text\<open>
                          Ejemplo de definición con existenciales
Un número natural n es par si existe un natural m tal que n=m+m.
\<close>
definition par :: "nat \<Rightarrow> bool" where
"par n \<equiv> \<exists>m. n=m+m"

text\<open>
Ejemplo de inducción y existenciales: Para todo número natural n, se verifica que n*(n+1) par.
\<close>
lemma
shows "par (n*(n+1))"
proof (induct n)
  show "par (0*(0+1))" by (simp add: par_def)
next
  fix n
  assume "par (n*(n+1))"
  hence "\<exists>m. n*(n+1) = m+m" by (simp add:par_def)
  then obtain m where m: "n*(n+1) = m+m" by (rule exE)
  hence "(Suc n)*((Suc n)+1) = (m+n+1)+(m+n+1)" by auto
  hence "\<exists>m. (Suc n)*((Suc n)+1) = m+m" by (rule exI)
  thus "par ((Suc n)*((Suc n)+1))" by (simp add:par_def)
qed

text\<open>
La suma de dos numeros pares es par:\<close>

lemma shows "par n \<and> par m \<longrightarrow> (par (n+m))"
proof(induct n)
  show "(par 0) \<and> (par m) \<longrightarrow> par (0 + m)" by auto
next
  fix n
  assume "par n \<and> par m \<longrightarrow> par (n + m)"
  show   "par (Suc n) \<and> par m \<longrightarrow> par (Suc n + m)"
  proof(rule impI)
    assume "par (Suc n) \<and> par m"
    hence  "(\<exists>m1. Suc n = m1+m1) \<and> (\<exists>m2. m = m2+m2)" 
      by (simp add:par_def)
    then obtain m1 m2 where "Suc n = m1+m1 \<and> m = m2+m2" 
      by auto
    hence "Suc (n + m) = (m1+m2)+(m1+m2)"  by auto
    hence "\<exists>k. Suc (n + m) = k+k" by auto
    thus  "par (Suc n + m)"  by (simp add:par_def)
  qed
qed


text\<open>
Definición en Isabelle de la función "par":

                                 even x \<leftarrow>\<rightarrow> x mod 2 = 0
\<close>

lemma
fixes n :: "nat"
shows "even (n*(n+1))"
  by auto

text\<open>
Equivalencia de las funciones "par" y "even"
\<close>

lemma
shows "par n = even n"
proof -
  have "par n = (\<exists>m. n = m+m)" by (simp add:par_def)
  thus "par n = even n" by presburger
qed
text\<open>
Otra forma de definir función par: \<close>

fun par1 :: "nat \<Rightarrow> bool" where
  "par1 0 = True" |
  "par1 (Suc 0) = False" |
  "par1 (Suc (Suc n)) = par1 n"

value "par1 31"

text\<open>
La anterior definición no es apropiada para demostrar propiedades sobre los números pares.
\<close>
text\<open>
             Todo tipo inductivo define un método de prueba de Inducción  Estrucutural
\<close>

end
text\<open> 
\<close>