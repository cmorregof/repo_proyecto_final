(* Ejercicios:  Deducción natural proposicional  *)

theory Ejercicios_Deduccion_natural
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
oops

text \<open> 
  Ejercicio 2. Demostrar
     (p \<longrightarrow> q) \<and> (p \<longrightarrow> r) \<turnstile> p \<longrightarrow> q \<and> r
   \<close>
lemma ejercicio_2:
  assumes 1: "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
  shows      "p \<longrightarrow> q \<and> r"
oops

text \<open> 
  Ejercicio 3. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> p \<and> q \<longrightarrow> r
   \<close>
lemma ejercicio_3:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows      "p \<and> q \<longrightarrow> r"
oops

text \<open> 
  Ejercicio 4. Demostrar
     q \<longrightarrow> r \<turnstile> p \<or> q \<longrightarrow> p \<or> r
   \<close>
lemma ejercicio_4:
  assumes 1: "q \<longrightarrow> r"
  shows      "p \<or> q \<longrightarrow> p \<or> r"
oops

text \<open> 
  Ejercicio 5. Demostrar
     (p \<or> q) \<or> r \<turnstile> p \<or> (q \<or> r)
   \<close>
lemma ejercicio_5:
  assumes 1: "(p \<or> q) \<or> r"
  shows       "p \<or> (q \<or> r)"
oops

text \<open> 
  Ejercicio 6. Demostrar
     p \<and> (q \<or> r) \<turnstile> (p \<and> q) \<or> (p \<and> r)
   \<close>
lemma ejercicio_6:
  assumes 1: "p \<and> (q \<or> r)"
  shows       "(p \<and> q) \<or> (p \<and> r)"
oops

text \<open> 
  Ejercicio 7. Demostrar
     (p \<and> q) \<or> (p \<and> r) \<turnstile> p \<and> (q \<or> r)
   \<close>
lemma ejercicio_7:
  assumes "(p \<and> q) \<or> (p \<and> r)"
  shows    "p \<and> (q \<or> r)"
oops

text \<open> 
  Ejercicio 8. Demostrar
     p \<or> (q \<and> r) \<turnstile> (p \<or> q) \<and> (p \<or> r)
   \<close>
lemma ejercicio_8:
  assumes "p \<or> (q \<and> r)"
  shows    "(p \<or> q) \<and> (p \<or> r)"
oops

text \<open> 
  Ejercicio 9. Demostrar
     (p \<or> q) \<and> (p \<or> r) \<turnstile> p \<or> (q \<and> r)
   \<close>
lemma ejercicio_9:
  assumes "(p \<or> q) \<and> (p \<or> r)"
  shows    "p \<or> (q \<and> r)"
oops

text \<open> 
  Ejercicio 10. Demostrar
     (p \<longrightarrow> r) \<and> (q \<longrightarrow> r) \<turnstile> p \<or> q \<longrightarrow> r
   \<close>
lemma ejercicio_10:
  assumes "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
  shows    "p \<or> q \<longrightarrow> r"
oops

text \<open> 
  Ejercicio 11. Demostrar
     p \<or> q \<longrightarrow> r \<turnstile> (p \<longrightarrow> r) \<and> (q \<longrightarrow> r)
   \<close>
lemma ejercicio_11:
  assumes "p \<or> q \<longrightarrow> r"
  shows    "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
oops

text \<open> 
  Ejercicio 12. Demostrar
     \<not>p \<turnstile> p \<longrightarrow> q
   \<close>
lemma ejercicio_12:
  assumes "\<not>p"
  shows   "p \<longrightarrow> q"
oops

text \<open> 
  Ejercicio 13. Demostrar
     p \<longrightarrow> q \<turnstile> \<not>q \<longrightarrow> \<not>p
   \<close>
lemma ejercicio_13:
  assumes "p \<longrightarrow> q"
  shows   "\<not>q \<longrightarrow> \<not>p"
oops

text \<open> 
  Ejercicio 14. Demostrar
     p \<or> q, \<not>q \<turnstile> p
   \<close>
lemma ejercicio_14:
  assumes "p \<or> q"
          "\<not>q"
  shows   "p"
oops

text \<open> 
  Ejercicio 15. Demostrar
     p \<or> q, \<not>p \<turnstile> q
   \<close>
lemma ejercicio_15:
  assumes "p \<or> q"
          "\<not>p"
  shows   "q"
oops

text \<open> 
  Ejercicio 16. Demostrar
     p \<or> q \<turnstile> \<not>(\<not>p \<and> \<not>q)
   \<close>
lemma ejercicio_16:
  assumes "p \<or> q"
  shows   "\<not>(\<not>p \<and> \<not>q)"
oops

text \<open> 
  Ejercicio 17. Demostrar
     p \<and> q \<turnstile> \<not>(\<not>p \<or> \<not>q)
   \<close>
lemma ejercicio_17:
  assumes "p \<and> q"
  shows   "\<not>(\<not>p \<or> \<not>q)"
oops

text \<open> 
  Ejercicio 18. Demostrar
     \<not>(p \<or> q) \<turnstile> \<not>p \<and> \<not>q
   \<close>
lemma ejercicio_18:
  assumes "\<not>(p \<or> q)"
  shows    "\<not>p \<and> \<not>q"
oops

text \<open> 
  Ejercicio 19. Demostrar
     \<not>p \<and> \<not>q \<turnstile> \<not>(p \<or> q)
   \<close>
lemma ejercicio_19:
  assumes "\<not>p \<and> \<not>q"
  shows   "\<not>(p \<or> q)"
oops

text \<open> 
  Ejercicio 20. Demostrar
     \<not>p \<or> \<not>q \<turnstile> \<not>(p \<and> q)
   \<close>
lemma ejercicio_20:
  assumes "\<not>p \<or> \<not>q"
  shows   "\<not>(p \<and> q)"
oops

text \<open> 
  Ejercicio 21. Demostrar
     \<turnstile> \<not>(p \<and> \<not>p)
   \<close>
lemma ejercicio_21:
  "\<not>(p \<and> \<not>p)"
oops

text \<open> 
  Ejercicio 22. Demostrar
     \<turnstile> ((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p
   \<close>
lemma ejercicio_22:
  "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
oops

text \<open> 
  Ejercicio 23. Demostrar
     \<not>(\<not>p \<and> \<not>q) \<turnstile> p \<or> q
   \<close>
lemma ejercicio_23:
  assumes "\<not>(\<not>p \<and> \<not>q)"
  shows   "p \<or> q"
oops

text \<open> 
  Ejercicio 24. Demostrar
     \<not>(\<not>p \<or> \<not>q) \<turnstile> p \<and> q
   \<close>
lemma ejercicio_24:
  assumes "\<not>(\<not>p \<or> \<not>q)"
  shows    "p \<and> q"
oops

end
