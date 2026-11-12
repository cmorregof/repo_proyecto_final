(* Deducción natural proposicional --- enunciados para el estudiante.
   Fuente: Alonso (2018), capitulo 3. CC BY-NC-SA. *)

theory R1_Deduccion_natural_enunciados
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


section \<open> Implicaciones \<close>


text \<open> 
  Ejercicio 1. Demostrar
       p \<longrightarrow> q, p \<turnstile> q
   \<close>
lemma ejercicio_1:
  assumes 1: "p \<longrightarrow> q" and
          2: "p"
  shows "q"
oops


text \<open> 
  Ejercicio 2. Demostrar
     p \<longrightarrow> q, q \<longrightarrow> r, p \<turnstile> r
   \<close>
lemma ejercicio_2:
  assumes 1: "p \<longrightarrow> q" and
          2: "q \<longrightarrow> r" and
          3: "p"
  shows "r"
oops


text \<open> 
  Ejercicio 3. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r), p \<longrightarrow> q, p \<turnstile> r
   \<close>
lemma ejercicio_3:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)" and
          2: "p \<longrightarrow> q" and
          3: "p"
  shows "r"
oops


text \<open> 
  Ejercicio 4. Demostrar
     p \<longrightarrow> q, q \<longrightarrow> r \<turnstile> p \<longrightarrow> r
   \<close>
lemma ejercicio_4:
  assumes 1: "p \<longrightarrow> q" and
          2: "q \<longrightarrow> r"
  shows "p \<longrightarrow> r"
oops


text \<open> 
  Ejercicio 5. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> q \<longrightarrow> (p \<longrightarrow> r)
   \<close>
lemma ejercicio_5:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "q \<longrightarrow> (p \<longrightarrow> r)"
oops


text \<open> 
  Ejercicio 6. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> (p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)
   \<close>
lemma ejercicio_6:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "(p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)"
oops


text \<open> 
  Ejercicio 7. Demostrar
     p \<turnstile> q \<longrightarrow> p
   \<close>
lemma ejercicio_7:
  assumes 1: "p"
  shows      "q \<longrightarrow> p"
oops


text \<open> 
  Ejercicio 8. Demostrar
     \<turnstile> p \<longrightarrow> (q \<longrightarrow> p)
   \<close>
lemma ejercicio_8:
  "p \<longrightarrow> (q \<longrightarrow> p)"
oops


text \<open> 
  Ejercicio 9. Demostrar
     p \<longrightarrow> q \<turnstile> (q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)
   \<close>
lemma ejercicio_9:
  assumes 1: "p \<longrightarrow> q"
  shows      "(q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)"
oops


text \<open> 
  Ejercicio 10. Demostrar
     p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s)) \<turnstile> r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))
   \<close>
lemma ejercicio_10:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows      "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
oops


text \<open> 
  Ejercicio 11. Demostrar
     \<turnstile> (p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))
   \<close>
lemma ejercicio_11:
  "(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))"
oops


text \<open> 
  Ejercicio 12. Demostrar
     (p \<longrightarrow> q) \<longrightarrow> r \<turnstile> p \<longrightarrow> (q \<longrightarrow> r)
   \<close>
lemma ejercicio_12:
  assumes 1: "(p \<longrightarrow> q) \<longrightarrow> r"
  shows      "p \<longrightarrow> (q \<longrightarrow> r)"
oops


section \<open> Conjunciones \<close>


text \<open> 
  Ejercicio 13. Demostrar
     p, q \<turnstile> p \<and> q
   \<close>
lemma ejercicio_13:
  assumes 1: "p" and
          2: "q"
  shows "p \<and> q"
oops


text \<open> 
  Ejercicio 14. Demostrar
     p \<and> q \<turnstile> p
   \<close>
lemma ejercicio_14:
  assumes 1: "p \<and> q"
  shows      "p"
oops


text \<open> 
  Ejercicio 15. Demostrar
     p \<and> q \<turnstile> q
   \<close>
lemma ejercicio_15:
  assumes 1: "p \<and> q"
  shows      "q"
oops


text \<open> 
  Ejercicio 16. Demostrar
     p \<and> (q \<and> r) \<turnstile> (p \<and> q) \<and> r
   \<close>
lemma ejercicio_16:
  assumes 1: "p \<and> (q \<and> r)"
  shows      "(p \<and> q) \<and> r"
oops


text \<open> 
  Ejercicio 17. Demostrar
     (p \<and> q) \<and> r \<turnstile> p \<and> (q \<and> r)
   \<close>
lemma ejercicio_17:
  assumes 1: "(p \<and> q) \<and> r"
  shows      "p \<and> (q \<and> r)"
oops


text \<open> 
  Ejercicio 18. Demostrar
     p \<and> q \<turnstile> p \<longrightarrow> q
   \<close>
lemma ejercicio_18:
  assumes 1: "p \<and> q"
  shows      "p \<longrightarrow> q"
oops


text \<open> 
  Ejercicio 19. Demostrar
     (p \<longrightarrow> q) \<and> (p \<longrightarrow> r) \<turnstile> p \<longrightarrow> q \<and> r
   \<close>
lemma ejercicio_19:
  assumes 1: "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
  shows      "p \<longrightarrow> q \<and> r"
oops


text \<open> 
  Ejercicio 20. Demostrar
     p \<longrightarrow> q \<and> r \<turnstile> (p \<longrightarrow> q) \<and> (p \<longrightarrow> r)
   \<close>
lemma ejercicio_20:
  assumes 1: "p \<longrightarrow> q \<and> r"
  shows      "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
oops


text \<open> 
  Ejercicio 21. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> p \<and> q \<longrightarrow> r
   \<close>
lemma ejercicio_21:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows      "p \<and> q \<longrightarrow> r"
oops


text \<open> 
  Ejercicio 22. Demostrar
     p \<and> q \<longrightarrow> r \<turnstile> p \<longrightarrow> (q \<longrightarrow> r)
   \<close>
lemma ejercicio_22:
  assumes 1: "p \<and> q \<longrightarrow> r"
  shows      "p \<longrightarrow> (q \<longrightarrow> r)"
oops


text \<open> 
  Ejercicio 23. Demostrar
     (p \<longrightarrow> q) \<longrightarrow> r \<turnstile> p \<and> q \<longrightarrow> r
   \<close>
lemma ejercicio_23:
  assumes 1: "(p \<longrightarrow> q) \<longrightarrow> r"
  shows      "p \<and> q \<longrightarrow> r"
oops


text \<open> 
  Ejercicio 24. Demostrar
     p \<and> (q \<longrightarrow> r) \<turnstile> (p \<longrightarrow> q) \<longrightarrow> r
   \<close>
lemma ejercicio_24:
  assumes 1: "p \<and> (q \<longrightarrow> r)"
  shows      "(p \<longrightarrow> q) \<longrightarrow> r"
oops


section \<open> Disyunciones \<close>


text \<open> 
  Ejercicio 25. Demostrar
     p \<turnstile> p \<or> q
   \<close>
lemma ejercicio_25:
  assumes 1: "p"
  shows      "p \<or> q"
oops


text \<open> 
  Ejercicio 26. Demostrar
     q \<turnstile> p \<or> q
   \<close>
lemma ejercicio_26:
  assumes 1: "q"
  shows      "p \<or> q"
oops


text \<open> 
  Ejercicio 27. Demostrar
     p \<or> q \<turnstile> q \<or> p
   \<close>
lemma ejercicio_27:
  assumes 1: "p \<or> q"
  shows      "q \<or> p"
oops


text \<open> 
  Ejercicio 28. Demostrar
     q \<longrightarrow> r \<turnstile> p \<or> q \<longrightarrow> p \<or> r
   \<close>
lemma ejercicio_28:
  assumes 1: "q \<longrightarrow> r"
  shows      "p \<or> q \<longrightarrow> p \<or> r"
oops


text \<open> 
  Ejercicio 29. Demostrar
     p \<or> p \<turnstile> p
   \<close>
lemma ejercicio_29:
  assumes 1: "p \<or> p"
  shows      "p"
oops


text \<open> 
  Ejercicio 30. Demostrar
     p \<turnstile> p \<or> p
   \<close>
lemma ejercicio_30:
  assumes 1: "p"
  shows      "p \<or> p"
oops


text \<open> 
  Ejercicio 31. Demostrar
     p \<or> (q \<or> r) \<turnstile> (p \<or> q) \<or> r
   \<close>
lemma ejercicio_31:
  assumes 1: "p \<or> (q \<or> r)"
  shows      "(p \<or> q) \<or> r"
oops


text \<open> 
  Ejercicio 32. Demostrar
     (p \<or> q) \<or> r \<turnstile> p \<or> (q \<or> r)
   \<close>
lemma ejercicio_32:
  assumes 1: "(p \<or> q) \<or> r"
  shows      "p \<or> (q \<or> r)"
oops


text \<open> 
  Ejercicio 33. Demostrar
     p \<and> (q \<or> r) \<turnstile> (p \<and> q) \<or> (p \<and> r)
   \<close>
lemma ejercicio_33:
  assumes 1: "p \<and> (q \<or> r)"
  shows      "(p \<and> q) \<or> (p \<and> r)"
oops


text \<open> 
  Ejercicio 34. Demostrar
     (p \<and> q) \<or> (p \<and> r) \<turnstile> p \<and> (q \<or> r)
   \<close>
lemma ejercicio_34:
  assumes "(p \<and> q) \<or> (p \<and> r)"
  shows   "p \<and> (q \<or> r)"
oops


text \<open> 
  Ejercicio 35. Demostrar
     p \<or> (q \<and> r) \<turnstile> (p \<or> q) \<and> (p \<or> r)
   \<close>
lemma ejercicio_35:
  assumes "p \<or> (q \<and> r)"
  shows   "(p \<or> q) \<and> (p \<or> r)"
oops


text \<open> 
  Ejercicio 36. Demostrar
     (p \<or> q) \<and> (p \<or> r) \<turnstile> p \<or> (q \<and> r)
   \<close>
lemma ejercicio_36:
  assumes "(p \<or> q) \<and> (p \<or> r)"
  shows   "p \<or> (q \<and> r)"
oops


text \<open> 
  Ejercicio 37. Demostrar
     (p \<longrightarrow> r) \<and> (q \<longrightarrow> r) \<turnstile> p \<or> q \<longrightarrow> r
   \<close>
lemma ejercicio_37:
  assumes "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
  shows   "p \<or> q \<longrightarrow> r"
oops


text \<open> 
  Ejercicio 38. Demostrar
     p \<or> q \<longrightarrow> r \<turnstile> (p \<longrightarrow> r) \<and> (q \<longrightarrow> r)
   \<close>
lemma ejercicio_38:
  assumes "p \<or> q \<longrightarrow> r"
  shows   "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
oops


section \<open> Negación \<close>

text \<open> 
  Ejercicio 39. Demostrar
     p \<turnstile> \<not>\<not>p
   \<close>
lemma ejercicio_39:
  assumes "p"
  shows   "\<not>\<not>p"
oops


text \<open> 
  Ejercicio 40. Demostrar
     \<not>p \<turnstile> p \<longrightarrow> q
   \<close>
lemma ejercicio_40:
  assumes "\<not>p"
  shows   "p \<longrightarrow> q"
oops

text \<open> 
  Ejercicio 41. Demostrar
     p \<longrightarrow> q \<turnstile> \<not>q \<longrightarrow> \<not>p
   \<close>
lemma ejercicio_41:
  assumes "p \<longrightarrow> q"
  shows   "\<not>q \<longrightarrow> \<not>p"
oops
    
text \<open> 
  Ejercicio 42. Demostrar
     p \<or> q, \<not>q \<turnstile> p
   \<close>
lemma ejercicio_42:
  assumes "p \<or> q"
          "\<not>q"
  shows   "p"
oops
    
text \<open> 
  Ejercicio 43. Demostrar
     p \<or> q, \<not>p \<turnstile> q
   \<close>
lemma ejercicio_43:
  assumes "p \<or> q"
          "\<not>p"
  shows   "q"
oops

text \<open> 
  Ejercicio 44. Demostrar
     p \<or> q \<turnstile> \<not>(\<not>p \<and> \<not>q)
   \<close>
lemma ejercicio_44:
  assumes "p \<or> q"
  shows   "\<not>(\<not>p \<and> \<not>q)" using assms
oops
text \<open> 
  Ejercicio 45. Demostrar
     p \<and> q \<turnstile> \<not>(\<not>p \<or> \<not>q)
   \<close>
lemma ejercicio_45:
  assumes "p \<and> q"
  shows   "\<not>(\<not>p \<or> \<not>q)"
oops

text \<open> 
  Ejercicio 46. Demostrar
     \<not>(p \<or> q) \<turnstile> \<not>p \<and> \<not>q
   \<close>
lemma ejercicio_46:
  assumes "\<not>(p \<or> q)"
  shows    "\<not>p \<and> \<not>q"
oops

text \<open> 
  Ejercicio 47. Demostrar
     \<not>p \<and> \<not>q \<turnstile> \<not>(p \<or> q)
   \<close>
lemma ejercicio_47:
  assumes "\<not>p \<and> \<not>q"
  shows   "\<not>(p \<or> q)"
oops


text \<open> 
  Ejercicio 48. Demostrar
     \<not>p \<or> \<not>q \<turnstile> \<not>(p \<and> q)
   \<close>
lemma ejercicio_48:
  assumes "\<not>p \<or> \<not>q"
  shows   "\<not>(p \<and> q)"
oops


text \<open> 
  Ejercicio 49. Demostrar
     \<turnstile> \<not>(p \<and> \<not>p)
   \<close>
lemma ejercicio_49:
  "\<not>(p \<and> \<not>p)"
oops


text \<open> 
  Ejercicio 50. Demostrar
     p \<and> \<not>p \<turnstile> q
   \<close>
lemma ejercicio_50:
  assumes "p \<and> \<not>p"
  shows   "q"
oops


text \<open> 
  Ejercicio 51. Demostrar
     \<not>\<not>p \<turnstile> p
   \<close>
lemma ejercicio_51:
  assumes "\<not>\<not>p"
  shows   "p"
oops


text \<open> 
  Ejercicio 52. Demostrar
     \<turnstile> p \<or> \<not>p
   \<close>
lemma ejercicio_52:
  "p \<or> \<not>p"
oops


text \<open> 
  Ejercicio 53. Demostrar
     \<turnstile> ((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p
   \<close>
lemma ejercicio_53:
  "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
oops


text \<open> 
  Ejercicio 54. Demostrar
     \<not>q \<longrightarrow> \<not>p \<turnstile> p \<longrightarrow> q
   \<close>
lemma ejercicio_54:
  assumes "\<not>q \<longrightarrow> \<not>p"
  shows    "p \<longrightarrow> q"
oops


text \<open> 
  Ejercicio 55. Demostrar
     \<not>(\<not>p \<and> \<not>q) \<turnstile> p \<or> q
   \<close>
lemma ejercicio_55:
  assumes "\<not>(\<not>p \<and> \<not>q)"
  shows   "p \<or> q"
oops
 
text \<open> 
  Ejercicio 56. Demostrar
     \<not>(\<not>p \<or> \<not>q) \<turnstile> p \<and> q
   \<close>
lemma ejercicio_56:
  assumes "\<not>(\<not>p \<or> \<not>q)"
  shows    "p \<and> q"
oops


text \<open> 
  Ejercicio 57. Demostrar
     \<not>(p \<and> q) \<turnstile> \<not>p \<or> \<not>q
   \<close>

lemma ejercicio_57:
  assumes "\<not>(p \<and> q)"
  shows    "\<not>p \<or> \<not>q"
  oops

text \<open> 
  Ejercicio 58. Demostrar
     \<turnstile> (p \<longrightarrow> q) \<or> (q \<longrightarrow> p)
   \<close>
lemma ejercicio_58:
  "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)"
oops

end
