(* T2_Deduccion_natural_en_logica_de_primer_orden
   Tema 2 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T2_Deduccion_natural_en_logica_de_primer_orden
imports Main
begin

chapter \<open> Tema 2: Deducción natural en lógica de primer orden \<close>
text \<open>
  El objetivo de este tema es presentar la deducción natural en
  lógica de primer orden con Isabelle/HOL. La presentación se
  basa en los ejemplos de tema 8 del curso LMF que se encuentra
  en http://goo.gl/uJj8d (que a su vez se basa en el libro de
  Huth y Ryan "Logic in Computer Science" http://goo.gl/qsVpY ).

  La página al lado de cada ejemplo indica la página de las
  transparencias de LMF donde se encuentra la demostración. \<close>

section \<open> Reglas del cuantificador universal \<close>

text \<open>
  Las reglas del cuantificador universal son
  \<sqdot> allE:    \<lbrakk>\<forall>x. P x; P a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
  \<sqdot> allI:    (\<And>x. P x) \<Longrightarrow> \<forall>x. P x

  \<close>

text \<open>

     Ejemplo 1 (p. 10). Demostrar que
        P(c), \<forall>x. (P(x) \<longrightarrow> \<not>Q(x)) \<turnstile> \<not>Q(c)
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_1a:
  assumes 1: "P(c)" and
          2: "\<forall>x. (P(x) \<longrightarrow> \<not>Q(x))"
  shows "\<not>Q(c)"
proof -
  have 3: "P(c) \<longrightarrow> \<not>Q(c)" using 2 by (rule allE)
  show 4: "\<not>Q(c)" using 3 1 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_1b:
  assumes "P(c)"
          "\<forall>x. (P(x) \<longrightarrow> \<not>Q(x))"
  shows "\<not>Q(c)"
proof -
  have "P(c) \<longrightarrow> \<not>Q(c)" using assms(2) ..
  thus "\<not>Q(c)" using assms(1) ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_1c:
  assumes "P(c)"
          "\<forall>x. (P(x) \<longrightarrow> \<not>Q(x))"
  shows "\<not>Q(c)"
using assms
by auto

text \<open>
   Ejemplo 2 (p. 11). Demostrar que
      \<forall>x. (P x \<longrightarrow> \<not>(Q x)), \<forall>x. P x \<turnstile> \<forall>x. \<not>(Q x)
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_2a:
  assumes 1: "\<forall>x. (P x \<longrightarrow> \<not>(Q x))" and
          2: "\<forall>x. P x"
  shows "\<forall>x. \<not>(Q x)"
proof -
  { fix a
    have 3: "P a \<longrightarrow> \<not>(Q a)" using 1 by (rule allE)
    have 4: "P a" using 2 by (rule allE)
    have 5: "\<not>(Q a)" using 3 4 by (rule mp) }
  thus "\<forall>x. \<not>(Q x)" by (rule allI)
qed

text \<open>La demostración detallada hacia atrás es\<close>
lemma ejemplo_2b:
  assumes 1: "\<forall>x. (P x \<longrightarrow> \<not>(Q x))" and
          2: "\<forall>x. P x"
  shows "\<forall>x. \<not>(Q x)"
proof (rule allI)
  fix a
  have 3: "P a \<longrightarrow> \<not>(Q a)" using 1 by (rule allE)
  have 4: "P a" using 2 by (rule allE)
  show 5: "\<not>(Q a)" using 3 4 by (rule mp)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_2c:
  assumes "\<forall>x. (P x \<longrightarrow> \<not>(Q x))"
          "\<forall>x. P x"
  shows "\<forall>x. \<not>(Q x)"
proof
  fix a
  have "P a" using assms(2) ..
  have "P a \<longrightarrow> \<not>(Q a)" using assms(1) ..
  thus "\<not>(Q a)" using `P a` ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_2d:
  assumes "\<forall>x. (P x \<longrightarrow> \<not>(Q x))"
          "\<forall>x. P x"
  shows "\<forall>x. \<not>(Q x)"
using assms

by auto

section \<open> Reglas del cuantificador existencial \<close>

text \<open>
  Las reglas del cuantificador existencial son
  \<sqdot> exI:     P a \<Longrightarrow> \<exists>x. P x
  \<sqdot> exE:     \<lbrakk>\<exists>x. P x;\<And>x. P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q

     En la regla exE la nueva variable se introduce mediante la declaración
     "obtain ... where ... by (rule exE)"
     \<close>

text \<open>
   Ejemplo (p. 12). Demostrar que
      \<forall>x. P x \<turnstile> \<exists>x. P x
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_3a:
  assumes "\<forall>x. P x"
  shows "\<exists>x. P x"
proof -
  fix a
  have "P a" using assms by (rule allE)
  thus "\<exists>x. P x" by (rule exI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_3b:
  assumes "\<forall>x. P x"
  shows "\<exists>x. P x"
proof -
  fix a
  have "P a" using assms ..
  thus "\<exists>x. P x" ..
qed

text \<open>La demostración estructurada se puede simplificar\<close>
lemma ejemplo_3c:

  assumes "\<forall>x. P x"
  shows "\<exists>x. P x"
proof (rule exI)
  fix a
  show "P a" using assms ..
qed

text \<open>La demostración estructurada se puede simplificar aún más\<close>
lemma ejemplo_3d:
  assumes "\<forall>x. P x"
  shows "\<exists>x. P x"
proof
  fix a
  show "P a" using assms ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_3e:
  assumes "\<forall>x. P x"
  shows "\<exists>x. P x"
using assms
by auto

text \<open>
   Ejemplo 4 (p. 13). Demostrar
      \<forall>x. (P x \<longrightarrow> Q x), \<exists>x. P x \<turnstile> \<exists>x. Q x
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_4a:
  assumes 1: "\<forall>x. (P x \<longrightarrow> Q x)" and
          2: "\<exists>x. P x"
  shows "\<exists>x. Q x"
proof -
  obtain a where 3: "P a" using 2 by (rule exE)
  have 4: "P a \<longrightarrow> Q a" using 1 by (rule allE)
  have 5: "Q a" using 4 3 by (rule mp)
  thus 6: "\<exists>x. Q x" by (rule exI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_4b:
  assumes "\<forall>x. (P x \<longrightarrow> Q x)"
          "\<exists>x. P x"
  shows "\<exists>x. Q x"
proof -
  obtain a where "P a" using assms(2) ..
  have "P a \<longrightarrow> Q a" using assms(1) ..
  hence "Q a" using `P a` ..
  thus "\<exists>x. Q x" ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_4c:
  assumes "\<forall>x. (P x \<longrightarrow> Q x)"
          "\<exists>x. P x"
  shows "\<exists>x. Q x"
using assms
by auto

section \<open> Demostración de equivalencias \<close>

text \<open>
  Ejemplo 5.1 (p. 15). Demostrar
     \<not>\<forall>x. P x \<turnstile> \<exists>x. \<not>(P x) \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_5_1a:
  assumes "\<not>(\<forall>x. P(x))"
  shows "\<exists>x. \<not>P(x)"
proof (rule ccontr)
  assume "\<not>(\<exists>x. \<not>P(x))"
  have "\<forall>x. P(x)"
  proof (rule allI)
    fix a
    show "P(a)"
    proof (rule ccontr)
      assume "\<not>P(a)"
      hence "\<exists>x. \<not>P(x)" by (rule exI)
      with `\<not>(\<exists>x. \<not>P(x))` show False by (rule notE)
    qed
  qed
  with assms show False by (rule notE)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_5_1b:
  assumes "\<not>(\<forall>x. P(x))"
  shows "\<exists>x. \<not>P(x)"
proof (rule ccontr)
  assume "\<not>(\<exists>x. \<not>P(x))"
  have "\<forall>x. P(x)"
  proof
    fix a
    show "P(a)"
    proof (rule ccontr)
      assume "\<not>P(a)"
      hence "\<exists>x. \<not>P(x)" ..
      with `\<not>(\<exists>x. \<not>P(x))` show False ..
    qed
  qed
  with assms show False ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_5_1c:
  assumes "\<not>(\<forall>x. P(x))"
  shows "\<exists>x. \<not>P(x)"
using assms
by auto

text \<open>
  Ejemplo 5.2 (p. 16). Demostrar
     \<exists>x. \<not>(P x) \<turnstile> \<not>\<forall>x. P x \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_5_2a:
  assumes "\<exists>x. \<not>P(x)"
  shows "\<not>(\<forall>x. P(x))"
proof (rule notI)

  assume "\<forall>x. P(x)"
  obtain a where "\<not>P(a)" using assms by (rule exE)
  have "P(a)" using `\<forall>x. P(x)` by (rule allE)
  with `\<not>P(a)` show False by (rule notE)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_5_2b:
  assumes "\<exists>x. \<not>P(x)"
  shows "\<not>(\<forall>x. P(x))"
proof
  assume "\<forall>x. P(x)"
  obtain a where "\<not>P(a)" using assms ..
  have "P(a)" using `\<forall>x. P(x)` ..
  with `\<not>P(a)` show False ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_5_2c:
  assumes "\<exists>x. \<not>P(x)"
  shows "\<not>(\<forall>x. P(x))"
using assms
by auto

text \<open>
  Ejemplo 5.3 (p. 17). Demostrar
     \<turnstile> \<not>\<forall>x. P x \<longleftrightarrow> \<exists>x. \<not>(P x) \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_5_3a:
  "(\<not>(\<forall>x. P(x))) \<longleftrightarrow> (\<exists>x. \<not>P(x))"
proof (rule iffI)
  assume "\<not>(\<forall>x. P(x))"
  thus "\<exists>x. \<not>P(x)" by (rule ejemplo_5_1a)
next
  assume "\<exists>x. \<not>P(x)"
  thus "\<not>(\<forall>x. P(x))" by (rule ejemplo_5_2a)
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_5_3b:
  "(\<not>(\<forall>x. P(x))) \<longleftrightarrow> (\<exists>x. \<not>P(x))"
by auto

text \<open>
  Ejemplo 6.1 (p. 18). Demostrar
     \<forall>x. P(x) \<and> Q(x) \<turnstile> (\<forall>x. P(x)) \<and> (\<forall>x. Q(x)) \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_6_1a:
  assumes "\<forall>x. P(x) \<and> Q(x)"
  shows "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
proof (rule conjI)
  show "\<forall>x. P(x)"
  proof (rule allI)
     fix a
     have "P(a) \<and> Q(a)" using assms by (rule allE)
     thus "P(a)" by (rule conjunct1)
  qed
next
  show "\<forall>x. Q(x)"
  proof (rule allI)
     fix a
     have "P(a) \<and> Q(a)" using assms by (rule allE)
     thus "Q(a)" by (rule conjunct2)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_6_1b:
  assumes "\<forall>x. P(x) \<and> Q(x)"
  shows "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
proof
  show "\<forall>x. P(x)"
  proof
     fix a
     have "P(a) \<and> Q(a)" using assms ..
     thus "P(a)" ..
  qed
next

  show "\<forall>x. Q(x)"
  proof
    fix a
    have "P(a) \<and> Q(a)" using assms ..
    thus "Q(a)" ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_6_1c:
  assumes "\<forall>x. P(x) \<and> Q(x)"
  shows "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
using assms
by auto

text \<open>
  Ejemplo 6.2 (p. 19). Demostrar
     (\<forall>x. P(x)) \<and> (\<forall>x. Q(x)) \<turnstile> \<forall>x. P(x) \<and> Q(x)      \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_6_2a:
  assumes "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
  shows "\<forall>x. P(x) \<and> Q(x)"
proof (rule allI)
  fix a
  have "\<forall>x. P(x)" using assms by (rule conjunct1)
  hence "P(a)" by (rule allE)
  have "\<forall>x. Q(x)" using assms by (rule conjunct2)
  hence "Q(a)" by (rule allE)
  with `P(a)` show "P(a) \<and> Q(a)" by (rule conjI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_6_2b:
  assumes "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
  shows "\<forall>x. P(x) \<and> Q(x)"
proof
  fix a
  have "\<forall>x. P(x)" using assms ..
  hence "P(a)" by (rule allE)

  have "\<forall>x. Q(x)" using assms ..
  hence "Q(a)" ..
  with `P(a)` show "P(a) \<and> Q(a)" ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_6_2c:
  assumes "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
  shows "\<forall>x. P(x) \<and> Q(x)"
using assms
by auto

text \<open>
  Ejemplo 6.3 (p. 20). Demostrar
     \<turnstile> \<forall>x. P(x) \<and> Q(x) \<longleftrightarrow> (\<forall>x. P(x)) \<and> (\<forall>x. Q(x)) \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_6_3a:
  "(\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> ((\<forall>x. P(x)) \<and> (\<forall>x. Q(x)))"
proof (rule iffI)
  assume "\<forall>x. P(x) \<and> Q(x)"
  thus "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))" by (rule ejemplo_6_1a)
next
  assume "(\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
  thus "\<forall>x. P(x) \<and> Q(x)" by (rule ejemplo_6_2a)
qed

text \<open>
  Ejemplo 7.1 (p. 21). Demostrar
     (\<exists>x. P(x)) \<or> (\<exists>x. Q(x)) \<turnstile> \<exists>x. P(x) \<or> Q(x)   \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_7_1a:
  assumes "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
  shows "\<exists>x. P(x) \<or> Q(x)"
using assms
proof (rule disjE)
  assume "\<exists>x. P(x)"
  then obtain a where "P(a)" by (rule exE)
  hence "P(a) \<or> Q(a)" by (rule disjI1)

  thus "\<exists>x. P(x) \<or> Q(x)" by (rule exI)
next
  assume "\<exists>x. Q(x)"
  then obtain a where "Q(a)" by (rule exE)
  hence "P(a) \<or> Q(a)" by (rule disjI2)
  thus "\<exists>x. P(x) \<or> Q(x)" by (rule exI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_7_1b:
  assumes "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
  shows "\<exists>x. P(x) \<or> Q(x)"
using assms
proof
  assume "\<exists>x. P(x)"
  then obtain a where "P(a)" ..
  hence "P(a) \<or> Q(a)" ..
  thus "\<exists>x. P(x) \<or> Q(x)" ..
next
  assume "\<exists>x. Q(x)"
  then obtain a where "Q(a)" ..
  hence "P(a) \<or> Q(a)" ..
  thus "\<exists>x. P(x) \<or> Q(x)" ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_7_1c:
  assumes "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
  shows "\<exists>x. P(x) \<or> Q(x)"
using assms
by auto

text \<open>
  Ejemplo 7.2 (p. 22). Demostrar
     \<exists>x. P(x) \<or> Q(x) \<turnstile> (\<exists>x. P(x)) \<or> (\<exists>x. Q(x)) \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_7_2a:
  assumes "\<exists>x. P(x) \<or> Q(x)"
  shows "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"

proof -
  obtain a where "P(a) \<or> Q(a)" using assms by (rule exE)
  thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
  proof (rule disjE)
    assume "P(a)"
    hence "\<exists>x. P(x)" by (rule exI)
    thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))" by (rule disjI1)
  next
    assume "Q(a)"
    hence "\<exists>x. Q(x)" by (rule exI)
    thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))" by (rule disjI2)
  qed
qed

text \<open>La demostración estructurada es\<close>
lemma ejercicio_7_2b:
  assumes "\<exists>x. P(x) \<or> Q(x)"
  shows "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
proof -
  obtain a where "P(a) \<or> Q(a)" using assms ..
  thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
  proof
    assume "P(a)"
    hence "\<exists>x. P(x)" ..
    thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))" ..
  next
    assume "Q(a)"
    hence "\<exists>x. Q(x)" ..
    thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))" ..
  qed
qed

text \<open>La demostración automática es\<close>
lemma ejercicio_7_2c:
  assumes "\<exists>x. P(x) \<or> Q(x)"
  shows "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
using assms
by auto

text \<open>

     Ejemplo 7.3 (p. 23). Demostrar
        \<turnstile> ((\<exists>x. P(x)) \<or> (\<exists>x. Q(x))) \<longleftrightarrow> (\<exists>x. P(x) \<or> Q(x))     \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_7_3a:
  "((\<exists>x. P(x)) \<or> (\<exists>x. Q(x))) \<longleftrightarrow> (\<exists>x. P(x) \<or> Q(x))"
proof (rule iffI)
  assume "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))"
  thus "\<exists>x. P(x) \<or> Q(x)" by (rule ejemplo_7_1a)
next
  assume "\<exists>x. P(x) \<or> Q(x)"
  thus "(\<exists>x. P(x)) \<or> (\<exists>x. Q(x))" by (rule ejemplo_7_2a)
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_7_3b:
  "((\<exists>x. P(x)) \<or> (\<exists>x. Q(x))) \<longleftrightarrow> (\<exists>x. P(x) \<or> Q(x))"
by auto

text \<open>
  Ejemplo 8.1 (p. 24). Demostrar
     \<exists>x y. P(x,y) \<turnstile> \<exists>y x. P(x,y)   \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_8_1a:
  assumes "\<exists>x y. P(x,y)"
  shows "\<exists>y x. P(x,y)"
proof -
  obtain a where "\<exists>y. P(a,y)" using assms by (rule exE)
  then obtain b where "P(a,b)" by (rule exE)
  hence "\<exists>x. P(x,b)" by (rule exI)
  thus "\<exists>y x. P(x,y)" by (rule exI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_8_1b:
  assumes "\<exists>x y. P(x,y)"
  shows "\<exists>y x. P(x,y)"
proof -

  obtain a where "\<exists>y. P(a,y)" using assms ..
  then obtain b where "P(a,b)" ..
  hence "\<exists>x. P(x,b)" ..
  thus "\<exists>y x. P(x,y)" ..
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_8_1c:
  assumes "\<exists>x y. P(x,y)"
  shows "\<exists>y x. P(x,y)"
using assms
by auto

text \<open>
  Ejemplo 8.2. Demostrar
     \<exists>y x. P(x,y) \<turnstile> \<exists>x y. P(x,y)     \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_8_2a:
  assumes "\<exists>y x. P(x,y)"
  shows "\<exists>x y. P(x,y)"
proof -
  obtain b where "\<exists>x. P(x,b)" using assms by (rule exE)
  then obtain a where "P(a,b)" by (rule exE)
  hence "\<exists>y. P(a,y)" by (rule exI)
  thus "\<exists>x y. P(x,y)" by (rule exI)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_8_2b:
  assumes "\<exists>y x. P(x,y)"
  shows "\<exists>x y. P(x,y)"
proof -
  obtain b where "\<exists>x. P(x,b)" using assms ..
  then obtain a where "P(a,b)" ..
  hence "\<exists>y. P(a,y)" ..
  thus "\<exists>x y. P(x,y)" ..
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_8_2c:
  assumes "\<exists>y x. P(x,y)"
  shows "\<exists>x y. P(x,y)"
using assms
by auto

text \<open>
  Ejemplo 8.3 (p. 25). Demostrar
     \<turnstile> (\<exists>x y. P(x,y)) \<longleftrightarrow> (\<exists>y x. P(x,y))     \<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_8_3a:
  "(\<exists>x y. P(x,y)) \<longleftrightarrow> (\<exists>y x. P(x,y))"
proof (rule iffI)
  assume "\<exists>x y. P(x,y)"
  thus "\<exists>y x. P(x,y)" by (rule ejemplo_8_1a)
next
  assume "\<exists>y x. P(x,y)"
  thus "\<exists>x y. P(x,y)" by (rule ejemplo_8_2a)
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_8_3b:
  "(\<exists>x y. P(x,y)) \<longleftrightarrow> (\<exists>y x. P(x,y))"
by auto

section \<open> Reglas de la igualdad \<close>

text \<open>
   Las reglas básicas de la igualdad son:
   \<sqdot> refl: t = t
   \<sqdot> subst: \<lbrakk>s = t; P s\<rbrakk> \<Longrightarrow> P t
\<close>

text \<open>
   Ejemplo 9 (p. 27). Demostrar
      x+1 = 1+x, x+1 > 1 \<longrightarrow> x+1 > 0 \<turnstile> 1+x > 1 \<longrightarrow> 1+x > 0
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_9a:
  assumes "x+1 = 1+x"
          "x+1 > 1 \<longrightarrow> x+1 > 0"
  shows "1+x > 1 \<longrightarrow> 1+x > 0"
proof -
  show "1+x > 1 \<longrightarrow> 1+x > 0" using assms by (rule subst)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_9b:
  assumes "x+1 = 1+x"
          "x+1 > 1 \<longrightarrow> x+1 > 0"
  shows "1+x > 1 \<longrightarrow> 1+x > 0"
using assms
by (rule subst)

text \<open>La demostración automática es\<close>
lemma ejemplo_9c:
  assumes "x+1 = 1+x"
          "x+1 > 1 \<longrightarrow> x+1 > 0"
  shows "1+x > 1 \<longrightarrow> 1+x > 0"
using assms
by auto

text \<open>
   Ejemplo 10 (p. 27). Demostrar
      x = y, y = z \<turnstile> x = z
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_10a:
  assumes "x = y"
          "y = z"
  shows "x = z"
proof -
  show "x = z" using assms(2,1) by (rule subst)
qed

text \<open>La demostración estructurada es\<close>
lemma ejemplo_10b:

  assumes "x = y"
          "y = z"
  shows "x = z"
using assms(2,1)
by (rule subst)

text \<open>La demostración automática es\<close>
lemma ejemplo_10c:
  assumes "x = y"
          "y = z"
  shows "x = z"
using assms
by auto

text \<open>
   Ejemplo 11 (p. 28). Demostrar
      s = t \<turnstile> t = s
\<close>

text \<open>La demostración detallada es\<close>
lemma ejemplo_11a:
  assumes "s = t"
  shows "t = s"
proof -
  have "s = s" by (rule refl)
  with assms show "t = s" by (rule subst)
qed

text \<open>La demostración automática es\<close>
lemma ejemplo_11b:
  assumes "s = t"
  shows "t = s"
using assms
by auto

end
