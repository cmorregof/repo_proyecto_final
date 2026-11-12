(* Ejercicios:  Deducción natural proposicional  *)

theory Ejercicios_Deduccion_natural_clase
imports Main
begin

chapter \<open>Deducción natural proposicional --- enunciados\<close>

text \<open>
  Demuestre cada lema usando solo las reglas basicas de deduccion
  natural. Sustituya cada \<open>oops\<close> por su demostracion.
\<close>

text \<open>Se usan las reglas notnotI y mt:\<close>

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
by auto

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto

text \<open> 
  Ejercicio 1. Demostrar
     p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s)) \<turnstile> r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))
   \<close>
lemma ejercicio_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows      "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
proof
  assume 2: "r"
  show "q \<longrightarrow> (p \<longrightarrow> s)"
  proof
    assume 3: "q"
    show "p \<longrightarrow> s"
    proof 
      assume 4:"p"
      have "q \<longrightarrow> (r \<longrightarrow> s)" using 1 4 ..
      hence "r \<longrightarrow>s" using 3 ..
      thus "s" using 2 ..
    qed
  qed
qed
    
lemma ejercicio_1a:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
proof
  assume "r"
  show "q \<longrightarrow> (p \<longrightarrow> s)"
  proof
    assume "q"
    show "p \<longrightarrow> s"
    proof
      assume "p"
      from 1 `p` have "q \<longrightarrow> (r \<longrightarrow> s)" by (rule mp)
      from this `q` have "r \<longrightarrow> s" by (rule mp)
      from this `r` show "s" by (rule mp)
    qed
  qed
qed

text \<open> 
  Ejercicio 2. Demostrar
     (p \<longrightarrow> q) \<and> (p \<longrightarrow> r) \<turnstile> p \<longrightarrow> q \<and> r
   \<close>
lemma ejercicio_2:
  assumes 1: "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
  shows      "p \<longrightarrow> q \<and> r"
proof
  assume 2:"p"
  show "q \<and> r"
  proof
    show "q"
    proof -
      have "p \<longrightarrow>q" using 1 by (rule conjunct1)
      thus "q" using 2 by (rule mp)
    qed
    show "r"
    proof -
      have "p \<longrightarrow>r"using 1 by (rule conjunct2)
      thus "r"using 2 by (rule mp)
    qed
  qed
qed
    
text \<open> 
  Ejercicio 4. Demostrar
     q \<longrightarrow> r \<turnstile> p \<or> q \<longrightarrow> p \<or> r
   \<close>
lemma ejercicio_4:
  assumes 1: "q \<longrightarrow> r"
  shows      "p \<or> q \<longrightarrow> p \<or> r"
proof
  assume 2: "p \<or> q"
  show " p \<or> r"
  proof -
    {assume 3: "p"
      have "p \<or>r" using 3 by (rule disjI1)}
    moreover
    {assume 3: "q"
      have "r" using 1 3 by (rule mp)
      hence "p \<or> r" by (rule disjI2)}
    ultimately
    show "p \<or> r" using 2 by auto
  qed
qed



end