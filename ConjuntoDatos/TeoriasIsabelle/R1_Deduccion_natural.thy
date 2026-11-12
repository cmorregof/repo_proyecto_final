(* Deducción natural proposicional --- soluciones
   Relacion de ejercicios del capitulo 3 de: Jose A. Alonso
   Jimenez, Demostracion asistida por ordenador con Isabelle/HOL,
   Universidad de Sevilla, 2018. Licencia CC BY-NC-SA.
   Portado a Isabelle2025-2. *)

theory R1_Deduccion_natural
imports Main
begin

text \<open>
  ---------------------------------------------------------------------
  El objetivo de esta relación es lemas usando sólo las reglas básicas
  de deducción natural de la lógica proposicional.

  Los ejercicios son los de la asignatura de "Lógica informática" que se
  encuentran en http://goo.gl/yrPLn

  Las reglas básicas de la deducción natural son las siguientes:

     \<sqdot> conjI:      \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q
     \<sqdot> conjunct1: P \<and> Q \<Longrightarrow> P
     \<sqdot> conjunct2: P \<and> Q \<Longrightarrow> Q
     \<sqdot> notnotD:    \<not>\<not> P \<Longrightarrow> P
     \<sqdot> notnotI:    P \<Longrightarrow> \<not>\<not> P
     \<sqdot> mp:         \<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q
     \<sqdot> mt:         \<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F
     \<sqdot> impI:       (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q
     \<sqdot> disjI1:     P \<Longrightarrow> P \<or> Q
     \<sqdot> disjI2:     Q \<Longrightarrow> P \<or> Q
     \<sqdot> disjE:      \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
     \<sqdot> FalseE:     False \<Longrightarrow> P
     \<sqdot> notE:       \<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> R
     \<sqdot> notI:       (P \<Longrightarrow> False) \<Longrightarrow> \<not>P
     \<sqdot> iffI:       \<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P = Q
     \<sqdot> iffD1:      \<lbrakk>Q = P; Q\<rbrakk> \<Longrightarrow> P
     \<sqdot> iffD2:      \<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P
     \<sqdot> ccontr:     (\<not>P \<Longrightarrow> False) \<Longrightarrow> P
     \<sqdot> excluded_middle: \<not>P \<or> P
     ---------------------------------------------------------------------
\<close>

text \<open>
  Se usarán las reglas notnotI y mt que demostramos a continuación.
  \<close>

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
by auto

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto

section \<open> Implicaciones \<close>

text \<open> ---------------------------------------------------------------
  Ejercicio 1. Demostrar
       p \<longrightarrow> q, p \<turnstile> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_1_1:
  assumes 1: "p \<longrightarrow> q" and
          2: "p"
  shows "q"
proof -

      show "q" using 1 2 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_1_2:
  assumes "p \<longrightarrow> q"
           "p"
  shows "q"
proof -
    show "q" using assms ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_1_3:
  assumes "p \<longrightarrow> q"
          "p"
  shows "q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 2. Demostrar
     p \<longrightarrow> q, q \<longrightarrow> r, p \<turnstile> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_2_1:
  assumes 1: "p \<longrightarrow> q" and
          2: "q \<longrightarrow> r" and
          3: "p"
  shows "r"
proof -
  have 4: "q" using 1 3 by (rule mp)
  show "r" using 2 4 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_2_2:
  assumes "p \<longrightarrow> q"
          "q \<longrightarrow> r"
          "p"
  shows "r"
proof -
  have "q" using assms(1,3) ..
  show "r" using assms(2) `q` ..

qed

text \<open>La demostración automática es\<close>
lemma ejercicio_2_3:
  assumes "p \<longrightarrow> q"
          "q \<longrightarrow> r"
          "p"
  shows "r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 3. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r), p \<longrightarrow> q, p \<turnstile> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_3_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)" and
          2: "p \<longrightarrow> q" and
          3: "p"
  shows "r"
proof -
  have 4: "q" using 2 3 by (rule mp)
  have 5: "q \<longrightarrow> r" using 1 3 by (rule mp)
  show "r" using 5 4 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_3_2:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
          "p \<longrightarrow> q"
          "p"
  shows   "r"
proof -
  have "q" using assms(2,3) ..
  have "q \<longrightarrow> r" using assms(1,3) ..
  thus "r" using `q` ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_3_3:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
          "p \<longrightarrow> q"
          "p"

  shows   "r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 4. Demostrar
     p \<longrightarrow> q, q \<longrightarrow> r \<turnstile> p \<longrightarrow> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_4_1:
  assumes 1: "p \<longrightarrow> q" and
          2: "q \<longrightarrow> r"
  shows "p \<longrightarrow> r"
proof (rule impI)
  assume 3: "p"
  have 4: "q" using 1 3 by (rule mp)
  show "r" using 2 4 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_4_2:
  assumes "p \<longrightarrow> q"
          "q \<longrightarrow> r"
  shows   "p \<longrightarrow> r"
proof
  assume "p"
  with assms(1) have "q" ..
  with assms(2) show "r" ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_4_3:
  assumes "p \<longrightarrow> q"
          "q \<longrightarrow> r"
  shows   "p \<longrightarrow> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 5. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> q \<longrightarrow> (p \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_5_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "q \<longrightarrow> (p \<longrightarrow> r)"
proof (rule impI)
  assume 2: "q"
  show "p \<longrightarrow> r"
  proof (rule impI)
    assume 3: "p"
    have "q \<longrightarrow> r" using 1 3 by (rule mp)
    thus "r" using 2 by (rule mp)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_5_2:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "q \<longrightarrow> (p \<longrightarrow> r)"
proof
  assume "q"
  show "p \<longrightarrow> r"
  proof
    assume "p"
    with assms(1) have "q \<longrightarrow> r" ..
    thus "r" using `q` ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_5_3:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "q \<longrightarrow> (p \<longrightarrow> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 6. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> (p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_6_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "(p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)"
proof (rule impI)
  assume 2: "p \<longrightarrow> q"

  show "p \<longrightarrow> r"
  proof (rule impI)
    assume 3: "p"
    have 4: "q" using 2 3 by (rule mp)
    have 5: "q \<longrightarrow> r" using 1 3 by (rule mp)
    show "r" using 5 4 by (rule mp)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_6_2:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "(p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)"
proof
  assume "p \<longrightarrow> q"
  show "p \<longrightarrow> r"
  proof
    assume "p"
    with `p \<longrightarrow> q` have "q" ..
    have "q \<longrightarrow> r" using assms(1) `p` ..
    thus "r" using `q` ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_6_3:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "(p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 7. Demostrar
     p \<turnstile> q \<longrightarrow> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_7_1:
  assumes 1: "p"
  shows      "q \<longrightarrow> p"
proof (rule impI)
  assume 2: "q"
  show "p" using 1 by this
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_7_2:
  assumes "p"
  shows   "q \<longrightarrow> p"
proof
  assume "q"
  show "p" using assms(1) .
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_7_3:
  assumes "p"
  shows   "q \<longrightarrow> p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 8. Demostrar
     \<turnstile> p \<longrightarrow> (q \<longrightarrow> p)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_8_1:
  "p \<longrightarrow> (q \<longrightarrow> p)"
proof (rule impI)
  assume 1: "p"
  show "q \<longrightarrow> p"
  proof (rule impI)
    assume 2: "q"
    show "p" using 1 by this
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_8_2:
  "p \<longrightarrow> (q \<longrightarrow> p)"
proof
  assume "p"
  show "q \<longrightarrow> p"
  proof
    assume "q"
    show "p" using `p` .
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_8_3:
  "p \<longrightarrow> (q \<longrightarrow> p)"
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 9. Demostrar
     p \<longrightarrow> q \<turnstile> (q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_9_1:
  assumes 1: "p \<longrightarrow> q"
  shows      "(q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)"
proof (rule impI)
  assume 2: "q \<longrightarrow> r"
  show "p \<longrightarrow> r"
  proof (rule impI)
    assume 3: "p"
    have 4: "q" using 1 3 by (rule mp)
    show "r" using 2 4 by (rule mp)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_9_2:
  assumes "p \<longrightarrow> q"
  shows   "(q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)"
proof
  assume "q \<longrightarrow> r"
  show "p \<longrightarrow> r"
  proof
    assume "p"
    with assms(1) have "q" ..
    with `q \<longrightarrow> r` show "r" ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_9_3:
  assumes "p \<longrightarrow> q"
  shows   "(q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 10. Demostrar
     p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s)) \<turnstile> r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_10_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows      "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
proof -
  { assume 2: "r"
    { assume 3: "q"
      { assume 4: "p"
        have 5: "q \<longrightarrow> (r \<longrightarrow> s)" using 1 4 by (rule mp)
        have 6: "r \<longrightarrow> s" using 5 3 by (rule mp)
        have 7: "s" using 6 2 by (rule mp) }
      hence 8: "p \<longrightarrow> s" by (rule impI) }
    hence 9: "q \<longrightarrow> (p \<longrightarrow> s)" by (rule impI) }
  thus 10: "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))" by (rule impI)
qed

text \<open>Una variante de la demostración anterior es\<close>
lemma ejercicio_10_1b:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows      "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
proof (rule impI)
  assume 2: "r"
  show "q \<longrightarrow> (p \<longrightarrow> s)"
  proof (rule impI)
    assume 3: "q"
    show "p \<longrightarrow> s"
    proof (rule impI)
      assume 4: "p"
      have 5: "q \<longrightarrow> (r \<longrightarrow> s)" using 1 4 by (rule mp)
      have 6: "r \<longrightarrow> s" using 5 3 by (rule mp)
      show "s" using 6 2 by (rule mp)
    qed
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_10_2:
  assumes "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows   "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
proof

  assume "r"
  show "q \<longrightarrow> (p \<longrightarrow> s)"
  proof
    assume "q"
    show "p \<longrightarrow> s"
    proof
      assume "p"
      with assms(1) have "q \<longrightarrow> (r \<longrightarrow> s)" ..
      hence "r \<longrightarrow> s" using `q` ..
      thus "s" using `r` ..
    qed
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_10_3:
  assumes "p \<longrightarrow> (q \<longrightarrow> (r \<longrightarrow> s))"
  shows   "r \<longrightarrow> (q \<longrightarrow> (p \<longrightarrow> s))"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 11. Demostrar
     \<turnstile> (p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_11_1:
  "(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))"
proof -
  { assume 1: "p \<longrightarrow> (q \<longrightarrow> r)"
    { assume 2: "p \<longrightarrow> q"
      { assume 3: "p"
        have 4: "q" using 2 3 by (rule mp)
        have 5: "q \<longrightarrow> r" using 1 3 by (rule mp)
        have 6: "r" using 5 4 by (rule mp) }
      hence 7: "p \<longrightarrow> r" by (rule impI) }
    hence 8: "(p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)" by (rule impI) }
  thus "(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))" by (rule impI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_11_2:
  "(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))"
proof

  assume "p \<longrightarrow> (q \<longrightarrow> r)"
  { assume "p \<longrightarrow> q"
    { assume "p"
      with `p \<longrightarrow> q` have "q" ..
      have "q \<longrightarrow> r" using `p \<longrightarrow> (q \<longrightarrow> r)` `p` ..
      hence "r" using `q` .. }
    hence "p \<longrightarrow> r" .. }
  thus "(p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r)" ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_11_3:
  "(p \<longrightarrow> (q \<longrightarrow> r)) \<longrightarrow> ((p \<longrightarrow> q) \<longrightarrow> (p \<longrightarrow> r))"
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 12. Demostrar
     (p \<longrightarrow> q) \<longrightarrow> r \<turnstile> p \<longrightarrow> (q \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_12_1:
  assumes 1: "(p \<longrightarrow> q) \<longrightarrow> r"
  shows      "p \<longrightarrow> (q \<longrightarrow> r)"
proof -
  { assume 2: "p"
    { assume 3: "q"
      { assume 4: "p"
        have 5: "q" using 3 by this }
      hence 6: "p \<longrightarrow> q" by (rule impI)
      have 7: "r" using 1 6 by (rule mp) }
    hence 8: "q \<longrightarrow> r" by (rule impI) }
  thus 9: "p \<longrightarrow> (q \<longrightarrow> r)" by (rule impI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_12_2:
  assumes "(p \<longrightarrow> q) \<longrightarrow> r"
  shows   "p \<longrightarrow> (q \<longrightarrow> r)"
proof
  assume "p"
  { assume "q"
    { assume "p"
      have "q" using `q` . }
    hence "p \<longrightarrow> q" ..

    with assms(1) have "r" .. }
  thus "q \<longrightarrow> r" ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_12_3:
  assumes "(p \<longrightarrow> q) \<longrightarrow> r"
  shows   "p \<longrightarrow> (q \<longrightarrow> r)"
using assms
by auto

section \<open> Conjunciones \<close>

text \<open> ---------------------------------------------------------------
  Ejercicio 13. Demostrar
     p, q \<turnstile> p \<and> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_13_1:
  assumes 1: "p" and
          2: "q"
  shows "p \<and> q"
proof -
  show "p \<and> q" using assms by (rule conjI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_13_2:
  assumes "p"
          "q"
  shows "p \<and> q"
proof
  show "p" using assms(1) .
next
  show "q" using assms(2) .
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_13_3:
  assumes "p"
          "q"
  shows "p \<and> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 14. Demostrar
     p \<and> q \<turnstile> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_14_1:
  assumes 1: "p \<and> q"
  shows      "p"
proof -
  show "p" using 1 by (rule conjunct1)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_14_2:
  assumes "p \<and> q"
  shows   "p"
proof -
  show "p" using assms ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_14_3:
  assumes "p \<and> q"
  shows   "p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 15. Demostrar
     p \<and> q \<turnstile> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_15_1:
  assumes 1: "p \<and> q"
  shows      "q"
proof -
  show "q" using 1 by (rule conjunct2)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_15_2:
  assumes "p \<and> q"

  shows   "q"
proof -
  show "q" using assms ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_15_3:
  assumes "p \<and> q"
  shows   "q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 16. Demostrar
     p \<and> (q \<and> r) \<turnstile> (p \<and> q) \<and> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_16_1:
  assumes 1: "p \<and> (q \<and> r)"
  shows      "(p \<and> q) \<and> r"
proof -
  have 2: "p" using 1 by (rule conjunct1)
  have 3: "q \<and> r" using 1 by (rule conjunct2)
  have 4: "q" using 3 by (rule conjunct1)
  have 5: "p \<and> q" using 2 4 by (rule conjI)
  have 6: "r" using 3 by (rule conjunct2)
  show 7: "(p \<and> q) \<and> r" using 5 6 by (rule conjI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_16_2:
  assumes "p \<and> (q \<and> r)"
  shows    "(p \<and> q) \<and> r"
proof
  show "p \<and> q"
  proof
     show "p" using assms ..
  next
     have "q \<and> r" using assms ..
     thus "q" ..
  qed
next
     have "q \<and> r" using assms ..
     thus "r" ..

qed

text \<open>La demostración automática es\<close>
lemma ejercicio_16_3:
  assumes "p \<and> (q \<and> r)"
  shows   "(p \<and> q) \<and> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 17. Demostrar
     (p \<and> q) \<and> r \<turnstile> p \<and> (q \<and> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_17_1:
  assumes 1: "(p \<and> q) \<and> r"
  shows      "p \<and> (q \<and> r)"
proof -
  have 2: "p \<and> q" using 1 by (rule conjunct1)
  have 3: "p" using 2 by (rule conjunct1)
  have 4: "q" using 2 by (rule conjunct2)
  have 5: "r" using 1 by (rule conjunct2)
  have 6: "q \<and> r" using 4 5 by (rule conjI)
  show 7: "p \<and> (q \<and> r)" using 3 6 by (rule conjI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_17_2:
  assumes "(p \<and> q) \<and> r"
  shows    "p \<and> (q \<and> r)"
proof
  have "p \<and> q" using assms ..
  thus "p" ..
next
  show "q \<and> r"
  proof
     have "p \<and> q" using assms ..
     thus "q" ..
  next
     show "r" using assms ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_17_3:
  assumes "(p \<and> q) \<and> r"
  shows   "p \<and> (q \<and> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 18. Demostrar
     p \<and> q \<turnstile> p \<longrightarrow> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_18_1:
  assumes 1: "p \<and> q"
  shows      "p \<longrightarrow> q"
proof (rule impI)
  assume 2: "p"
  show "q" using 1 by (rule conjunct2)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_18_2:
  assumes "p \<and> q"
  shows   "p \<longrightarrow> q"
proof
  assume "p"
  show "q" using assms ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_18_3:
  assumes "p \<and> q"
  shows   "p \<longrightarrow> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 19. Demostrar
     (p \<longrightarrow> q) \<and> (p \<longrightarrow> r) \<turnstile> p \<longrightarrow> q \<and> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_19_1:
  assumes 1: "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
  shows      "p \<longrightarrow> q \<and> r"

proof (rule impI)
  assume 2: "p"
  have 3: "p \<longrightarrow> q" using 1 by (rule conjunct1)
  have 4: "q" using 3 2 by (rule mp)
  have 5: "p \<longrightarrow> r" using 1 by (rule conjunct2)
  have 6: "r" using 5 2 by (rule mp)
  show 7: "q \<and> r" using 4 6 by (rule conjI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_19_2:
  assumes "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
  shows   "p \<longrightarrow> q \<and> r"
proof
  assume "p"
  show "q \<and> r"
  proof
    have "p \<longrightarrow> q" using assms ..
    thus "q" using `p` ..
  next
    have "p \<longrightarrow> r" using assms ..
    thus "r" using `p` ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_19_3:
  assumes "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
  shows   "p \<longrightarrow> q \<and> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 20. Demostrar
     p \<longrightarrow> q \<and> r \<turnstile> (p \<longrightarrow> q) \<and> (p \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_20_1:
  assumes 1: "p \<longrightarrow> q \<and> r"
  shows      "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
proof (rule conjI)
  show "p \<longrightarrow> q"
  proof (rule impI)
    assume 2: "p"

     have "q \<and> r" using 1 2 by (rule mp)
     thus "q" by (rule conjunct1)
  qed
next
  show "p \<longrightarrow> r"
  proof (rule impI)
     assume 3: "p"
     have "q \<and> r" using 1 3 by (rule mp)
     thus "r" by (rule conjunct2)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_20_2:
  assumes "p \<longrightarrow> q \<and> r"
  shows    "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
proof
  show "p \<longrightarrow> q"
  proof
     assume "p"
     have "q \<and> r" using assms `p` ..
     thus "q" ..
  qed
next
  show "p \<longrightarrow> r"
  proof
     assume "p"
     have "q \<and> r" using assms `p` ..
     thus "r" ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_20_3:
  assumes "p \<longrightarrow> q \<and> r"
  shows   "(p \<longrightarrow> q) \<and> (p \<longrightarrow> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 21. Demostrar
     p \<longrightarrow> (q \<longrightarrow> r) \<turnstile> p \<and> q \<longrightarrow> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_21_1:
  assumes 1: "p \<longrightarrow> (q \<longrightarrow> r)"
  shows      "p \<and> q \<longrightarrow> r"
proof (rule impI)
  assume 2: "p \<and> q"
  have 3: "p" using 2 by (rule conjunct1)
  have 4: "q" using 2 by (rule conjunct2)
  have 5: "q \<longrightarrow> r" using 1 3 by (rule mp)
  show 6: "r" using 5 4 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_21_2:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "p \<and> q \<longrightarrow> r"
proof
  assume "p \<and> q"
  hence "p" ..
  have "q" using `p \<and> q` ..
  have "q \<longrightarrow> r" using assms(1) `p` ..
  thus "r" using `q` ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_21_3:
  assumes "p \<longrightarrow> (q \<longrightarrow> r)"
  shows   "p \<and> q \<longrightarrow> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 22. Demostrar
     p \<and> q \<longrightarrow> r \<turnstile> p \<longrightarrow> (q \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_22_1:
  assumes 1: "p \<and> q \<longrightarrow> r"
  shows      "p \<longrightarrow> (q \<longrightarrow> r)"
proof (rule impI)
  assume 2: "p"
  { assume 3: "q"
    have 4: "p \<and> q" using 2 3 by (rule conjI)
    have "r" using 1 4 by (rule mp) }
  thus "q \<longrightarrow> r" by (rule impI)

qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_22_2:
  assumes "p \<and> q \<longrightarrow> r"
  shows   "p \<longrightarrow> (q \<longrightarrow> r)"
proof
  assume "p"
  show "q \<longrightarrow> r"
  proof
    assume "q"
    with `p` have "p \<and> q" ..
    with assms(1) show "r" ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_22_3:
  assumes "p \<and> q \<longrightarrow> r"
  shows   "p \<longrightarrow> (q \<longrightarrow> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 23. Demostrar
     (p \<longrightarrow> q) \<longrightarrow> r \<turnstile> p \<and> q \<longrightarrow> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_23_1:
  assumes 1: "(p \<longrightarrow> q) \<longrightarrow> r"
  shows      "p \<and> q \<longrightarrow> r"
proof (rule impI)
  assume 2: "p \<and> q"
  have 3: "p \<longrightarrow> q"
  proof (rule impI)
    assume 4: "p"
    show "q" using 2 by (rule conjunct2)
  qed
  show "r" using 1 3 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_23_2:
  assumes "(p \<longrightarrow> q) \<longrightarrow> r"

  shows   "p \<and> q \<longrightarrow> r"
proof
  assume "p \<and> q"
  have "p \<longrightarrow> q"
  proof
    assume "p"
    show "q" using `p \<and> q` ..
  qed
  with assms show "r" ..
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_23_3:
  assumes "(p \<longrightarrow> q) \<longrightarrow> r"
  shows   "p \<and> q \<longrightarrow> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 24. Demostrar
     p \<and> (q \<longrightarrow> r) \<turnstile> (p \<longrightarrow> q) \<longrightarrow> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_24_1:
  assumes 1: "p \<and> (q \<longrightarrow> r)"
  shows      "(p \<longrightarrow> q) \<longrightarrow> r"
proof (rule impI)
  assume 2: "p \<longrightarrow> q"
  have 3: "p" using 1 by (rule conjunct1)
  have 4: "q" using 2 3 by (rule mp)
  have 5: "q \<longrightarrow> r" using 1 by (rule conjunct2)
  thus "r" using 4 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_24_2:
  assumes "p \<and> (q \<longrightarrow> r)"
  shows   "(p \<longrightarrow> q) \<longrightarrow> r"
proof
  assume "p \<longrightarrow> q"
  have "p" using assms ..
  with `p \<longrightarrow> q` have "q" ..
  have "q \<longrightarrow> r" using assms ..
  thus "r" using `q` ..

qed

text \<open>La demostración automática es\<close>
lemma ejercicio_24_3:
  assumes "p \<and> (q \<longrightarrow> r)"
  shows   "(p \<longrightarrow> q) \<longrightarrow> r"
using assms
by auto

section \<open> Disyunciones \<close>

text \<open> ---------------------------------------------------------------
  Ejercicio 25. Demostrar
     p \<turnstile> p \<or> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_25_1:
  assumes 1: "p"
  shows      "p \<or> q"
proof -
  show "p \<or> q" using 1 by (rule disjI1)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_25_2:
  assumes "p"
  shows   "p \<or> q"
proof -
  show "p \<or> q" using assms ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_25_3:
  assumes "p"
  shows   "p \<or> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 26. Demostrar
     q \<turnstile> p \<or> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_26_1:
  assumes 1: "q"
  shows      "p \<or> q"
proof -
  show "p \<or> q" using 1 by (rule disjI2)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_26_2:
  assumes "q"
  shows   "p \<or> q"
proof -
  show "p \<or> q" using assms ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_26_3:
  assumes "q"
  shows   "p \<or> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 27. Demostrar
     p \<or> q \<turnstile> q \<or> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_27_1:
  assumes 1: "p \<or> q"
  shows      "q \<or> p"
using 1
proof (rule disjE)
  assume "p"
  thus "q \<or> p" by (rule disjI2)
next
  assume "q"
  thus "q \<or> p" by (rule disjI1)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_27_2:
  assumes "p \<or> q"
  shows   "q \<or> p"
using assms

proof
  assume "p"
  thus "q \<or> p" ..
next
  assume "q"
  thus "q \<or> p" ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_27_3:
  assumes "p \<or> q"
  shows   "q \<or> p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 28. Demostrar
     q \<longrightarrow> r \<turnstile> p \<or> q \<longrightarrow> p \<or> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_28_1:
  assumes 1: "q \<longrightarrow> r"
  shows      "p \<or> q \<longrightarrow> p \<or> r"
proof (rule impI)
  assume "p \<or> q"
  thus "p \<or> r"
  proof (rule disjE)
    assume "p"
    thus "p \<or> r" by (rule disjI1)
  next
    assume "q"
    have "r" using assms `q` by (rule mp)
    thus "p \<or> r" by (rule disjI2)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_28_2:
  assumes "q \<longrightarrow> r"
  shows   "p \<or> q \<longrightarrow> p \<or> r"
proof
  assume "p \<or> q"
  thus "p \<or> r"
  proof

    assume "p"
    thus "p \<or> r" ..
  next
    assume "q"
    have "r" using assms `q` ..
    thus "p \<or> r" ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_28_3:
  assumes "q \<longrightarrow> r"
  shows   "p \<or> q \<longrightarrow> p \<or> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 29. Demostrar
     p \<or> p \<turnstile> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_29_1:
  assumes 1: "p \<or> p"
  shows      "p"
using 1
proof (rule disjE)
  assume "p"
  thus "p" by this
next
  assume "p"
  thus "p" by this
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_29_2:
  assumes "p \<or> p"
  shows   "p"
using assms
proof
  assume "p"
  thus "p" .
next
  assume "p"
  thus "p" .

qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_29_3:
  assumes "p \<or> p"
  shows   "p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 30. Demostrar
     p \<turnstile> p \<or> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_30_1:
  assumes 1: "p"
  shows      "p \<or> p"
proof -
  show "p \<or> p" using 1 by (rule disjI1)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_30_2:
  assumes "p"
  shows   "p \<or> p"
proof -
  show "p \<or> p" using assms ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_30_3:
  assumes "p"
  shows   "p \<or> p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 31. Demostrar
     p \<or> (q \<or> r) \<turnstile> (p \<or> q) \<or> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_31_1:
  assumes 1: "p \<or> (q \<or> r)"

  shows       "(p \<or> q) \<or> r"
using 1
proof (rule disjE)
  assume "p"
  hence "p \<or> q" by (rule disjI1)
  thus "(p \<or> q) \<or> r" by (rule disjI1)
next
  assume "q \<or> r"
  thus "(p \<or> q) \<or> r"
  proof (rule disjE)
     assume "q"
     hence "p \<or> q" by (rule disjI2)
     thus "(p \<or> q) \<or> r" by (rule disjI1)
  next
     assume "r"
     thus "(p \<or> q) \<or> r" by (rule disjI2)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_31_2:
  assumes "p \<or> (q \<or> r)"
  shows    "(p \<or> q) \<or> r"
using assms
proof
  assume "p"
  hence "p \<or> q" ..
  thus "(p \<or> q) \<or> r" ..
next
  assume "q \<or> r"
  thus "(p \<or> q) \<or> r"
  proof
     assume "q"
     hence "p \<or> q" ..
     thus "(p \<or> q) \<or> r" ..
  next
     assume "r"
     thus "(p \<or> q) \<or> r" ..
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_31_3:
  assumes "p \<or> (q \<or> r)"
  shows   "(p \<or> q) \<or> r"

using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 32. Demostrar
     (p \<or> q) \<or> r \<turnstile> p \<or> (q \<or> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_32_1:
  assumes 1: "(p \<or> q) \<or> r"
  shows       "p \<or> (q \<or> r)"
using 1
proof (rule disjE)
  assume "p \<or> q"
  thus "p \<or> (q \<or> r)"
  proof (rule disjE)
     assume "p"
     thus "p \<or> (q \<or> r)" by (rule disjI1)
  next
     assume "q"
     hence "q \<or> r" by (rule disjI1)
     thus "p \<or> (q \<or> r)" by (rule disjI2)
  qed
next
  assume "r"
  hence "q \<or> r" by (rule disjI2)
  thus "p \<or> (q \<or> r)" by (rule disjI2)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_32_2:
  assumes "(p \<or> q) \<or> r"
  shows   "p \<or> (q \<or> r)"
using assms
proof
  assume "p \<or> q"
  thus "p \<or> (q \<or> r)"
  proof
    assume "p"
    thus "p \<or> (q \<or> r)" ..
  next
    assume "q"
    hence "q \<or> r" ..
    thus "p \<or> (q \<or> r)" ..

  qed
next
  assume "r"
  hence "q \<or> r" ..
  thus "p \<or> (q \<or> r)" ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_32_3:
  assumes "(p \<or> q) \<or> r"
  shows   "p \<or> (q \<or> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 33. Demostrar
     p \<and> (q \<or> r) \<turnstile> (p \<and> q) \<or> (p \<and> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_33_1:
  assumes 1: "p \<and> (q \<or> r)"
  shows       "(p \<and> q) \<or> (p \<and> r)"
proof -
  have 2: "p" using 1 by (rule conjunct1)
  have 3: "q \<or> r" using 1 by (rule conjunct2)
  thus "(p \<and> q) \<or> (p \<and> r)"
  proof (rule disjE)
    assume 4: "q"
    have "p \<and> q" using 2 4 by (rule conjI)
    thus "(p \<and> q) \<or> (p \<and> r)" by (rule disjI1)
  next
    assume 5: "r"
    have "q \<or> r" using 1 by (rule conjunct2)
    thus "(p \<and> q) \<or> (p \<and> r)"
    proof (rule disjE)
       assume "q"
       have "p \<and> q" using `p` `q` by (rule conjI)
       thus "(p \<and> q) \<or> (p \<and> r)" by (rule disjI1)
    next
       assume "r"
       have "p \<and> r" using `p` `r` by (rule conjI)
       thus "(p \<and> q) \<or> (p \<and> r)" by (rule disjI2)
    qed
  qed

qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_33_2:
  assumes "p \<and> (q \<or> r)"
  shows    "(p \<and> q) \<or> (p \<and> r)"
proof -
  have "p" using assms ..
  have "q \<or> r" using assms ..
  thus "(p \<and> q) \<or> (p \<and> r)"
  proof
    assume "q"
    with `p` have "p \<and> q" ..
    thus "(p \<and> q) \<or> (p \<and> r)" ..
  next
    assume "r"
    hence "q \<or> r" ..
    thus "(p \<and> q) \<or> (p \<and> r)"
    proof
       assume "q"
       with `p` have "p \<and> q" ..
       thus "(p \<and> q) \<or> (p \<and> r)" ..
    next
       assume "r"
       with `p` have "p \<and> r" ..
       thus "(p \<and> q) \<or> (p \<and> r)" ..
    qed
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_33_3:
  assumes "p \<and> (q \<or> r)"
  shows   "(p \<and> q) \<or> (p \<and> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 34. Demostrar
     (p \<and> q) \<or> (p \<and> r) \<turnstile> p \<and> (q \<or> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_34_1:
  assumes "(p \<and> q) \<or> (p \<and> r)"

  shows    "p \<and> (q \<or> r)"
using assms
proof (rule disjE)
  assume 1: "p \<and> q"
  show "p \<and> (q \<or> r)"
  proof (rule conjI)
     show "p" using 1 by (rule conjunct1)
  next
     have "q" using 1 by (rule conjunct2)
     thus "q \<or> r" by (rule disjI1)
  qed
next
  assume 2: "p \<and> r"
  hence 3: "p" by (rule conjunct1)
  have "r" using 2 by (rule conjunct2)
  hence 4: "q \<or> r" by (rule disjI2)
  show "p \<and> (q \<or> r)" using 3 4 by (rule conjI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_34_2:
  assumes "(p \<and> q) \<or> (p \<and> r)"
  shows    "p \<and> (q \<or> r)"
using assms
proof
  assume "p \<and> q"
  show "p \<and> (q \<or> r)"
  proof
     show "p" using `p \<and> q` ..
  next
     have "q" using `p \<and> q` ..
     thus "q \<or> r" ..
  qed
next
  assume "p \<and> r"
  hence "p" ..
  have "r" using `p \<and> r` ..
  hence "q \<or> r" ..
  with `p` show "p \<and> (q \<or> r)" ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_34_3:
  assumes "(p \<and> q) \<or> (p \<and> r)"
  shows   "p \<and> (q \<or> r)"

using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 35. Demostrar
     p \<or> (q \<and> r) \<turnstile> (p \<or> q) \<and> (p \<or> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_35_1:
  assumes "p \<or> (q \<and> r)"
  shows    "(p \<or> q) \<and> (p \<or> r)"
using assms
proof
  assume "p"
  show "(p \<or> q) \<and> (p \<or> r)"
  proof
     show "p \<or> q" using `p` ..
  next
     show "p \<or> r" using `p` ..
  qed
next
  assume "q \<and> r"
  show "(p \<or> q) \<and> (p \<or> r)"
  proof
     have "q" using `q \<and> r` ..
     thus "p \<or> q" ..
  next
     have "r" using `q \<and> r` ..
     thus "p \<or> r" ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_35_2:
  assumes "p \<or> (q \<and> r)"
  shows   "(p \<or> q) \<and> (p \<or> r)"
using assms
proof (rule disjE)
  assume "p"
  show "(p \<or> q) \<and> (p \<or> r)"
  proof (rule conjI)
    show "p \<or> q" using `p` by (rule disjI1)
  next
    show "p \<or> r" using `p` by (rule disjI1)

  qed
next
  assume "q \<and> r"
  show "(p \<or> q) \<and> (p \<or> r)"
  proof (rule conjI)
     have "q" using `q \<and> r` ..
     thus "p \<or> q" by (rule disjI2)
  next
     have "r" using `q \<and> r` by (rule conjunct2)
     thus "p \<or> r" by (rule disjI2)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_35_3:
  assumes "p \<or> (q \<and> r)"
  shows   "(p \<or> q) \<and> (p \<or> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 36. Demostrar
     (p \<or> q) \<and> (p \<or> r) \<turnstile> p \<or> (q \<and> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_36_1:
  assumes "(p \<or> q) \<and> (p \<or> r)"
  shows    "p \<or> (q \<and> r)"
proof -
  have "p \<or> q" using assms ..
  thus "p \<or> (q \<and> r)"
  proof
    assume "p"
    thus "p \<or> (q \<and> r)" ..
  next
    assume "q"
    have "p \<or> r" using assms ..
    thus "p \<or> (q \<and> r)"
    proof
       assume "p"
       thus "p \<or> (q \<and> r)" ..
    next
       assume "r"
       with `q` have "q \<and> r" ..

      thus "p \<or> (q \<and> r)" ..
    qed
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_36_2:
  assumes "(p \<or> q) \<and> (p \<or> r)"
  shows    "p \<or> (q \<and> r)"
proof -
  have "p \<or> q" using assms by (rule conjunct1)
  thus "p \<or> (q \<and> r)"
  proof (rule disjE)
    assume "p"
    thus "p \<or> (q \<and> r)" by (rule disjI1)
  next
    assume "q"
    have "p \<or> r" using assms by (rule conjunct2)
    thus "p \<or> (q \<and> r)"
    proof (rule disjE)
       assume "p"
       thus "p \<or> (q \<and> r)" by (rule disjI1)
    next
       assume "r"
       have "q \<and> r" using `q` `r` by (rule conjI)
       thus "p \<or> (q \<and> r)" by (rule disjI2)
    qed
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_36_3:
  assumes "(p \<or> q) \<and> (p \<or> r)"
  shows   "p \<or> (q \<and> r)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 37. Demostrar
     (p \<longrightarrow> r) \<and> (q \<longrightarrow> r) \<turnstile> p \<or> q \<longrightarrow> r
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_37_1:
  assumes "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"

  shows    "p \<or> q \<longrightarrow> r"
proof
  assume "p \<or> q"
  thus "r"
  proof
    assume "p"
    have "p \<longrightarrow> r" using assms ..
    thus "r" using `p` ..
  next
    assume "q"
    have "q \<longrightarrow> r" using assms ..
    thus "r" using `q` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_37_2:
  assumes "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
  shows    "p \<or> q \<longrightarrow> r"
proof (rule impI)
  assume "p \<or> q"
  thus "r"
  proof (rule disjE)
    assume "p"
    have "p \<longrightarrow> r" using assms by (rule conjunct1)
    thus "r" using `p` by (rule mp)
  next
    assume "q"
    have "q \<longrightarrow> r" using assms by (rule conjunct2)
    thus "r" using `q` by (rule mp)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_37_3:
  assumes "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
  shows   "p \<or> q \<longrightarrow> r"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 38. Demostrar
     p \<or> q \<longrightarrow> r \<turnstile> (p \<longrightarrow> r) \<and> (q \<longrightarrow> r)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_38_1:
  assumes "p \<or> q \<longrightarrow> r"
  shows    "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
proof
  show "p \<longrightarrow> r"
  proof
     assume "p"
     hence "p \<or> q" ..
     with assms show "r" ..
  qed
next
  show "q \<longrightarrow> r"
  proof
     assume "q"
     hence "p \<or> q" ..
     with assms show "r" ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_38_2:
  assumes "p \<or> q \<longrightarrow> r"
  shows    "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
proof (rule conjI)
  show "p \<longrightarrow> r"
  proof (rule impI)
     assume "p"
     hence "p \<or> q" by (rule disjI1)
     show "r" using assms `p \<or> q` by (rule mp)
  qed
next
  show "q \<longrightarrow> r"
  proof (rule impI)
     assume "q"
     hence "p \<or> q" by (rule disjI2)
     show "r" using assms `p \<or> q` by (rule mp)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_38_3:
  assumes "p \<or> q \<longrightarrow> r"
  shows   "(p \<longrightarrow> r) \<and> (q \<longrightarrow> r)"
using assms

by auto

section \<open> Negación \<close>

text \<open> ---------------------------------------------------------------
  Ejercicio 39. Demostrar
     p \<turnstile> \<not>\<not>p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_39_1:
  assumes "p"
  shows   "\<not>\<not>p"
proof -
  show "\<not>\<not>p" using assms by (rule notnotI)
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_39_2:
  assumes "p"
  shows   "\<not>\<not>p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 40. Demostrar
     \<not>p \<turnstile> p \<longrightarrow> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_40_1:
  assumes "\<not>p"
  shows   "p \<longrightarrow> q"
proof
  assume "p"
  with assms(1) show "q" ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_40_2:
  assumes "\<not>p"
  shows   "p \<longrightarrow> q"
proof (rule impI)
  assume "p"
  show "q" using assms(1) `p` by (rule notE)

qed

text \<open>La demostración automática es\<close>
lemma ejercicio_40_3:
  assumes "\<not>p"
  shows   "p \<longrightarrow> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 41. Demostrar
     p \<longrightarrow> q \<turnstile> \<not>q \<longrightarrow> \<not>p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_41_1:
  assumes "p \<longrightarrow> q"
  shows   "\<not>q \<longrightarrow> \<not>p"
proof
  assume "\<not>q"
  with assms(1) show "\<not>p" by (rule mt)
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_41_2:
  assumes "p \<longrightarrow> q"
  shows   "\<not>q \<longrightarrow> \<not>p"
proof (rule impI)
  assume "\<not>q"
  show "\<not>p" using assms(1) `\<not>q` by (rule mt)
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_41_3:
  assumes "p \<longrightarrow> q"
  shows   "\<not>q \<longrightarrow> \<not>p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 42. Demostrar
     p \<or> q, \<not>q \<turnstile> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_42_1:
  assumes "p \<or> q"
          "\<not>q"
  shows   "p"
using assms(1)
proof
  assume "p"
  thus "p" .
next
  assume "q"
  with assms(2) show "p" ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_42_2:
  assumes "p \<or> q"
          "\<not>q"
  shows   "p"
using assms(1)
proof (rule disjE)
  assume "p"
  thus "p" by this
next
  assume "q"
  show "p" using assms(2) `q` by (rule notE)
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_42_3:
  assumes "p \<or> q"
          "\<not>q"
  shows   "p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 42. Demostrar
     p \<or> q, \<not>p \<turnstile> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_43_1:
  assumes "p \<or> q"
          "\<not>p"
  shows   "q"

using assms(1)
proof
  assume "p"
  with assms(2) show "q" ..
next
  assume "q"
  thus "q" .
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_43_2:
  assumes "p \<or> q"
          "\<not>p"
  shows   "q"
using assms(1)
proof (rule disjE)
  assume "p"
  show "q" using assms(2) `p` by (rule notE)
next
  assume "q"
  thus "q" by this
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_43_3:
  assumes "p \<or> q"
          "\<not>p"
  shows   "q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 44. Demostrar
     p \<or> q \<turnstile> \<not>(\<not>p \<and> \<not>q)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_44_1:
  assumes "p \<or> q"
  shows   "\<not>(\<not>p \<and> \<not>q)"
proof
  assume "\<not>p \<and> \<not>q"
  note `p \<or> q`
  thus "False"
  proof

    assume "p"
    have "\<not>p" using `\<not>p \<and> \<not>q` ..
    thus "False" using `p` ..
  next
    assume "q"
    have "\<not>q" using `\<not>p \<and> \<not>q` ..
    thus "False" using `q` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_44_2:
  assumes "p \<or> q"
  shows   "\<not>(\<not>p \<and> \<not>q)"
proof (rule notI)
  assume "\<not>p \<and> \<not>q"
  note `p \<or> q`
  thus "False"
  proof
    assume "p"
    have "\<not>p" using `\<not>p \<and> \<not>q` by (rule conjunct1)
    thus "False" using `p` by (rule notE)
  next
    assume "q"
    have "\<not>q" using `\<not>p \<and> \<not>q` by (rule conjunct2)
    thus "False" using `q` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_44_3:
  assumes "p \<or> q"
  shows   "\<not>(\<not>p \<and> \<not>q)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 45. Demostrar
     p \<and> q \<turnstile> \<not>(\<not>p \<or> \<not>q)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_45_1:
  assumes "p \<and> q"
  shows   "\<not>(\<not>p \<or> \<not>q)"

proof
  assume "\<not>p \<or> \<not>q"
  thus "False"
  proof
    assume "\<not>p"
    have "p" using assms ..
    with `\<not>p` show "False" ..
  next
    assume "\<not>q"
    have "q" using assms ..
    with `\<not>q` show "False" ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_45_2:
  assumes "p \<and> q"
  shows   "\<not>(\<not>p \<or> \<not>q)"
proof (rule notI)
  assume "\<not>p \<or> \<not>q"
  thus "False"
  proof
    assume "\<not>p"
    have "p" using assms by (rule conjunct1)
    show "False" using `\<not>p` `p` by (rule notE)
  next
    assume "\<not>q"
    have "q" using assms by (rule conjunct2)
    show "False" using `\<not>q` `q` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_45_3:
  assumes "p \<and> q"
  shows   "\<not>(\<not>p \<or> \<not>q)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 46. Demostrar
     \<not>(p \<or> q) \<turnstile> \<not>p \<and> \<not>q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_46_1:
  assumes "\<not>(p \<or> q)"
  shows    "\<not>p \<and> \<not>q"
proof
  show "\<not>p"
  proof
     assume "p"
     hence "p \<or> q" ..
     with assms show "False" ..
  qed
next
  show "\<not>q"
  proof
     assume "q"
     hence "p \<or> q" ..
     with assms show "False" ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_46_2:
  assumes "\<not>(p \<or> q)"
  shows    "\<not>p \<and> \<not>q"
proof (rule conjI)
  show "\<not>p"
  proof (rule notI)
     assume "p"
     hence "p \<or> q" by (rule disjI1)
     show "False" using assms `p \<or> q` by (rule notE)
  qed
next
  show "\<not>q"
  proof (rule notI)
     assume "q"
     hence "p \<or> q" by (rule disjI2)
     show "False" using assms `p \<or> q` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_46_3:
  assumes "\<not>(p \<or> q)"
  shows   "\<not>p \<and> \<not>q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 47. Demostrar
     \<not>p \<and> \<not>q \<turnstile> \<not>(p \<or> q)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_47_1:
  assumes "\<not>p \<and> \<not>q"
  shows   "\<not>(p \<or> q)"
proof
  assume "p \<or> q"
  thus False
  proof
    assume "p"
    have "\<not>p" using assms ..
    thus False using `p` ..
  next
    assume "q"
    have "\<not>q" using assms ..
    thus False using `q` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_47_2:
  assumes "\<not>p \<and> \<not>q"
  shows   "\<not>(p \<or> q)"
proof (rule notI)
  assume "p \<or> q"
  thus False
  proof (rule disjE)
    assume "p"
    have "\<not>p" using assms by (rule conjunct1)
    thus False using `p` by (rule notE)
  next
    assume "q"
    have "\<not>q" using assms by (rule conjunct2)
    thus False using `q` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_47_3:
  assumes "\<not>p \<and> \<not>q"

  shows   "\<not>(p \<or> q)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 48. Demostrar
     \<not>p \<or> \<not>q \<turnstile> \<not>(p \<and> q)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_48_1:
  assumes "\<not>p \<or> \<not>q"
  shows   "\<not>(p \<and> q)"
proof
  assume "p \<and> q"
  note `\<not>p \<or> \<not> q`
  thus False
  proof
    assume "\<not>p"
    have "p" using `p \<and> q` ..
    with `\<not>p` show False ..
  next
    assume "\<not>q"
    have "q" using `p \<and> q` ..
    with `\<not>q` show False ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_48_2:
  assumes "\<not>p \<or> \<not>q"
  shows   "\<not>(p \<and> q)"
proof (rule notI)
  assume "p \<and> q"
  note `\<not>p \<or> \<not> q`
  thus False
  proof (rule disjE)
    assume "\<not>p"
    have "p" using `p \<and> q` by (rule conjunct1)
    show False using `\<not>p` `p` by (rule notE)
  next
    assume "\<not>q"
    have "q" using `p \<and> q` by (rule conjunct2)
    show False using `\<not>q` `q` by (rule notE)
  qed

qed

text \<open>La demostración automática es\<close>
lemma ejercicio_48_3:
  assumes "\<not>p \<or> \<not>q"
  shows   "\<not>(p \<and> q)"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 49. Demostrar
     \<turnstile> \<not>(p \<and> \<not>p)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_49_1:
  "\<not>(p \<and> \<not>p)"
proof
  assume "p \<and> \<not>p"
  hence "p" ..
  have "\<not>p" using `p \<and> \<not>p` ..
  thus False using `p` ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_49_2:
  "\<not>(p \<and> \<not>p)"
proof (rule notI)
  assume "p \<and> \<not>p"
  hence "p" by (rule conjunct1)
  have "\<not>p" using `p \<and> \<not>p` by (rule conjunct2)
  thus False using `p` by (rule notE)
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_49_3:
  "\<not>(p \<and> \<not>p)"
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 50. Demostrar
     p \<and> \<not>p \<turnstile> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_50_1:
  assumes "p \<and> \<not>p"
  shows   "q"
proof -
  have "p" using assms ..
  have "\<not>p" using assms ..
  thus "q" using `p` ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_50_2:
  assumes "p \<and> \<not>p"
  shows   "q"
proof -
  have "p" using assms by (rule conjunct1)
  have "\<not>p" using assms by (rule conjunct2)
  thus "q" using `p` by (rule notE)
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_50_3:
  assumes "p \<and> \<not>p"
  shows   "q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 51. Demostrar
     \<not>\<not>p \<turnstile> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración detallada es\<close>
lemma ejercicio_51_1:
  assumes "\<not>\<not>p"
  shows   "p"
using assms
by (rule notnotD)

text \<open>La demostración automática es\<close>
lemma ejercicio_51_2:
  assumes "\<not>\<not>p"
  shows   "p"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 52. Demostrar
     \<turnstile> p \<or> \<not>p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_52_1:
  "p \<or> \<not>p"
proof -
  have "\<not>\<not>p \<or> \<not>p" ..
  thus "p \<or> \<not>p" by simp
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_52_2:
  "p \<or> \<not>p"
proof -
  have "\<not>\<not>p \<or> \<not>p" by (rule excluded_middle)
  thus "p \<or> \<not>p" by simp
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_52_3:
  "p \<or> \<not>p"
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 53. Demostrar
     \<turnstile> ((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_53_1:
  "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
proof
  assume "(p \<longrightarrow> q) \<longrightarrow> p"
  show "p"
  proof (rule ccontr)
    assume "\<not>p"
    have "\<not>(p \<longrightarrow> q)" using `(p \<longrightarrow> q) \<longrightarrow> p` `\<not>p` by (rule mt)
    have "p \<longrightarrow> q"
    proof
      assume "p"
      with `\<not>p` show "q" ..
    qed

    show False using `\<not>(p \<longrightarrow> q)` `p \<longrightarrow> q` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_53_2:
  "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
proof (rule impI)
  assume "(p \<longrightarrow> q) \<longrightarrow> p"
  show "p"
  proof (rule ccontr)
    assume "\<not>p"
    have "\<not>(p \<longrightarrow> q)" using `(p \<longrightarrow> q) \<longrightarrow> p` `\<not>p` by (rule mt)
    have "p \<longrightarrow> q"
    proof (rule impI)
      assume "p"
      show "q" using `\<not>p` `p` by (rule notE)
    qed
    show False using `\<not>(p \<longrightarrow> q)` `p \<longrightarrow> q` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_53_3:
  "((p \<longrightarrow> q) \<longrightarrow> p) \<longrightarrow> p"
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 54. Demostrar
     \<not>q \<longrightarrow> \<not>p \<turnstile> p \<longrightarrow> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_54_1:
  assumes "\<not>q \<longrightarrow> \<not>p"
  shows    "p \<longrightarrow> q"
proof
  assume "p"
  show "q"
  proof (rule ccontr)
    assume "\<not>q"
    with assms have "\<not>p" ..
    thus False using `p` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_54_2:
  assumes "\<not>q \<longrightarrow> \<not>p"
  shows    "p \<longrightarrow> q"
proof (rule impI)
  assume "p"
  show "q"
  proof (rule ccontr)
    assume "\<not>q"
    have "\<not>p" using assms `\<not>q` by (rule mp)
    thus False using `p` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_54_3:
  assumes "\<not>q \<longrightarrow> \<not>p"
  shows   "p \<longrightarrow> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 55. Demostrar
     \<not>(\<not>p \<and> \<not>q) \<turnstile> p \<or> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_55_1:
  assumes "\<not>(\<not>p \<and> \<not>q)"
  shows   "p \<or> q"
proof -
  have "\<not>p \<or> p" ..
  thus "p \<or> q"
  proof
    assume "\<not>p"
    have "\<not>q \<or> q" ..
    thus "p \<or> q"
    proof
      assume "\<not>q"
      with `\<not>p` have "\<not>p \<and> \<not>q" ..
      with assms show "p \<or> q" ..
    next
      assume "q"
      thus "p \<or> q" ..

    qed
  next
    assume "p"
    thus "p \<or> q" ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_55_2:
  assumes "\<not>(\<not>p \<and> \<not>q)"
  shows    "p \<or> q"
proof -
  have "\<not>p \<or> p" by (rule excluded_middle)
  thus "p \<or> q"
  proof
    assume "\<not>p"
    have "\<not>q \<or> q" by (rule excluded_middle)
    thus "p \<or> q"
    proof
       assume "\<not>q"
       have "\<not>p \<and> \<not>q" using `\<not>p` `\<not>q` by (rule conjI)
       show "p \<or> q" using assms `\<not>p \<and> \<not>q` by (rule notE)
    next
       assume "q"
       thus "p \<or> q" by (rule disjI2)
    qed
  next
    assume "p"
    thus "p \<or> q" by (rule disjI1)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_55_3:
  assumes "\<not>(\<not>p \<and> \<not>q)"
  shows   "p \<or> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 56. Demostrar
     \<not>(\<not>p \<or> \<not>q) \<turnstile> p \<and> q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_56_1:
  assumes "\<not>(\<not>p \<or> \<not>q)"
  shows    "p \<and> q"
proof
  show "p"
  proof (rule ccontr)
     assume "\<not>p"
     hence "\<not>p \<or> \<not>q" ..
     with assms show False ..
  qed
next
  show "q"
  proof (rule ccontr)
     assume "\<not>q"
     hence "\<not>p \<or> \<not>q" ..
     with assms show False ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_56_2:
  assumes "\<not>(\<not>p \<or> \<not>q)"
  shows    "p \<and> q"
proof (rule conjI)
  show "p"
  proof (rule ccontr)
     assume "\<not>p"
     hence "\<not>p \<or> \<not>q" by (rule disjI1)
     show False using assms `\<not>p \<or> \<not>q` by (rule notE)
  qed
next
  show "q"
  proof (rule ccontr)
     assume "\<not>q"
     hence "\<not>p \<or> \<not>q" by (rule disjI2)
     show False using assms `\<not>p \<or> \<not>q` by (rule notE)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_56_3:
  assumes "\<not>(\<not>p \<or> \<not>q)"
  shows   "p \<and> q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 57. Demostrar
     \<not>(p \<and> q) \<turnstile> \<not>p \<or> \<not>q
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_57_1:
  assumes "\<not>(p \<and> q)"
  shows    "\<not>p \<or> \<not>q"
proof -
  have "\<not>p \<or> p" ..
  thus "\<not>p \<or> \<not>q"
  proof
    assume "\<not>p"
    thus "\<not>p \<or> \<not>q" ..
  next
    assume "p"
    have "\<not>q \<or> q" ..
    thus "\<not>p \<or> \<not>q"
    proof
       assume "\<not>q"
       thus "\<not>p \<or> \<not>q" ..
    next
       assume "q"
       with `p` have "p \<and> q" ..
       with assms show "\<not>p \<or> \<not>q" ..
    qed
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_57_2:
  assumes "\<not>(p \<and> q)"
  shows   "\<not>p \<or> \<not>q"
proof -
  have "\<not>p \<or> p" by (rule excluded_middle)
  thus "\<not>p \<or> \<not>q"
  proof (rule disjE)
    assume "\<not>p"
    thus "\<not>p \<or> \<not>q" by (rule disjI1)
  next
    assume "p"
    have "\<not>q \<or> q" by (rule excluded_middle)
    thus "\<not>p \<or> \<not>q"

    proof
      assume "\<not>q"
      thus "\<not>p \<or> \<not>q" by (rule disjI2)
    next
      assume "q"
      have "p \<and> q" using `p` `q` by (rule conjI)
      show "\<not>p \<or> \<not>q" using assms `p \<and> q` by (rule notE)
    qed
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_57_3:
  assumes "\<not>(p \<and> q)"
  shows   "\<not>p \<or> \<not>q"
using assms
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 58. Demostrar
     \<turnstile> (p \<longrightarrow> q) \<or> (q \<longrightarrow> p)
  ------------------------------------------------------------------ \<close>

text \<open>La demostración estructurada es\<close>
lemma ejercicio_58_1:
  "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)"
proof -
  have "\<not>p \<or> p" ..
  thus "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)"
  proof
    assume "\<not>p"
    have "p \<longrightarrow> q"
    proof
       assume "p"
       with `\<not>p` show "q" ..
    qed
    thus "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)" ..
  next
    assume "p"
    have "q \<longrightarrow> p"
    proof
       assume "q"
       show "p" using `p` .
    qed
    thus "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)" ..

  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_58_2:
  "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)"
proof -
  have "\<not>p \<or> p" by (rule excluded_middle)
  thus "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)"
  proof
    assume "\<not>p"
    have "p \<longrightarrow> q"
    proof (rule impI)
       assume "p"
       show "q" using `\<not>p` `p` by (rule notE)
    qed
    thus "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)" by (rule disjI1)
  next
    assume "p"
    have "q \<longrightarrow> p"
    proof
       assume "q"
       show "p" using `p` by this
    qed
    thus "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)" by (rule disjI2)
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_58_3:
  "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)"
by auto

end
