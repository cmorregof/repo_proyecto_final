(* Deducción natural proposicional --- enunciados para el estudiante.
   Fuente: Alonso (2018), capitulo 3. CC BY-NC-SA. *)

theory Taller1_deduccion_natural
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
     p \<and> q \<turnstile> \<not>(\<not>p \<or> \<not>q)
   \<close>
lemma ejercicio_1:
  assumes "p \<and> q"
  shows   "\<not>(\<not>p \<or> \<not>q)"
oops

text \<open> 
  Ejercicio 2. Demostrar
     \<not>(p \<or> q) \<turnstile> \<not>p \<and> \<not>q
   \<close>
lemma ejercicio_2:
  assumes "\<not>(p \<or> q)"
  shows    "\<not>p \<and> \<not>q"
oops

text \<open> 
  Ejercicio 3. Demostrar
     \<not>p \<and> \<not>q \<turnstile> \<not>(p \<or> q)
   \<close>
lemma ejercicio_3:
  assumes "\<not>p \<and> \<not>q"
  shows   "\<not>(p \<or> q)"
oops


text \<open> 
  Ejercicio 4. Demostrar
     \<not>p \<or> \<not>q \<turnstile> \<not>(p \<and> q)
   \<close>
lemma ejercicio_4:
  assumes "\<not>p \<or> \<not>q"
  shows   "\<not>(p \<and> q)"
oops


text \<open> 
  Ejercicio 5. Demostrar
     \<turnstile> \<not>(p \<and> \<not>p)
   \<close>
lemma ejercicio_5:
  "\<not>(p \<and> \<not>p)"
oops

text \<open> 
  Ejercicio 6. Demostrar
     \<turnstile> ((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p
   \<close>
lemma ejercicio_6:
  "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
oops


text \<open> 
  Ejercicio 7. Demostrar
     \<not>q \<longrightarrow> \<not>p \<turnstile> p \<longrightarrow> q
   \<close>
lemma ejercicio_7:
  assumes "\<not>q \<longrightarrow> \<not>p"
  shows    "p \<longrightarrow> q"
oops


text \<open> 
  Ejercicio 8. Demostrar
     \<not>(\<not>p \<and> \<not>q) \<turnstile> p \<or> q
   \<close>
lemma ejercicio_8:
  assumes "\<not>(\<not>p \<and> \<not>q)"
  shows   "p \<or> q"
oops
 
text \<open> 
  Ejercicio 9. Demostrar
     \<not>(\<not>p \<or> \<not>q) \<turnstile> p \<and> q
   \<close>
lemma ejercicio_9:
  assumes "\<not>(\<not>p \<or> \<not>q)"
  shows    "p \<and> q"
oops


text \<open> 
  Ejercicio 10. Demostrar
     \<not>(p \<and> q) \<turnstile> \<not>p \<or> \<not>q
   \<close>

lemma ejercicio_10:
  assumes "\<not>(p \<and> q)"
  shows    "\<not>p \<or> \<not>q"
  oops

end

