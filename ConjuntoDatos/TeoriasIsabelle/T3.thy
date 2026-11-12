(* T3
   Tema 3 de las notas:

     Jose A. Alonso Jimenez. Introduccion a la demostracion asistida por
     ordenador con Isabelle/HOL. Grupo de Logica Computacional, Universidad
     de Sevilla, 2013. Licencia CC BY-NC-SA 2.5 Espana.

   Portado de Isabelle2013 a Isabelle2025-2 para el curso Razonamiento
   Automatico. La obra derivada conserva la licencia CC BY-NC-SA 2.5. *)

theory T3
imports Main
begin

chapter \<open> Tema 3: Resumen del lenguaje Isabelle/Isar y las reglas de la lógica \<close>
section \<open> Sintaxis (simplificada) de Isabelle/Isar \<close>

text \<open>
  Representación de lemas (y teoremas)
  \<sqdot> Un lema (o teorema) comienza con una etiqueta seguida por algunas
    premisas y una conclusión.
  \<sqdot> Las premisas se introducen con la palabra "assumes" y se separan
    con "and".
  \<sqdot> Cada premisa puede etiquetarse para referenciarse en la demostración.
  \<sqdot> La conclusión se introduce con la palabra "shows".

  Gramática (simplificada) de las demostraciones en Isabelle/Isar
  <demostración> ::= proof <método> <declaración>* qed
                   | by <método>
  <declaración> ::= fix <variable>+
                   | assume <proposición>+
                   | (from <hecho>+)? have <proposición>+ <demostración>
                   | (from <hecho>+)? show <proposición>+ <demostración>
  <proposición> ::= (<etiqueta>:)? <cadena>
  hecho          ::= <etiqueta>
  método         ::= -

                     | this
                     | rule <hecho>
                     | simp
                     | blast
                     | auto
                     | induct <variable>

     La declaración "show" demuestra la conclusión de la demostración
     mientras que la declaración "have" demuestra un resultado intermedio.
\<close>

section \<open> Atajos de Isabelle/Isar \<close>

text \<open>
   Isar tiene muchos atajos, como los siguientes:
   this        | éste           | el hecho probado en la declaración anterior
   then        | entonces       | from this
   hence       | por lo tanto | then have
   thus        | de esta manera | then show
   with hecho+ | con            | from hecho+ and this
   .           | por ésto       | by this
   ..          | trivialmente | by regla (Isabelle adivina la regla)
\<close>

section \<open> Resumen de las reglas de la lógica \<close>

text \<open>
  Resumen de reglas proposicionales:
  \<sqdot> TrueI:          True
  \<sqdot> conjI:          \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q
  \<sqdot> conjunct1:      P \<and> Q \<Longrightarrow> P
  \<sqdot> conjunct2:      P \<and> Q \<Longrightarrow> Q
  \<sqdot> conjE:          \<lbrakk>P \<and> Q; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
  \<sqdot> disjI1:         P \<Longrightarrow> P \<or> Q
  \<sqdot> disjI2:         Q \<Longrightarrow> P \<or> Q
  \<sqdot> disjE:          \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
  \<sqdot> notI:           (P \<Longrightarrow> False) \<Longrightarrow> \<not>P
  \<sqdot> notE:           \<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> R
  \<sqdot> FalseE:         False \<Longrightarrow> P
  \<sqdot> notnotD:        \<not>\<not> P \<Longrightarrow> P

     \<sqdot> impI:           (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q
     \<sqdot> impE:           \<lbrakk>P \<longrightarrow> Q; P; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
     \<sqdot> mp:             \<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q
     \<sqdot> iff:            (P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> P) \<longrightarrow> P = Q
     \<sqdot> iffI:           \<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P = Q
     \<sqdot> iffD1:          \<lbrakk>Q = P; Q\<rbrakk> \<Longrightarrow> P
     \<sqdot> iffD2:          \<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P
     \<sqdot> iffE:           \<lbrakk>P = Q; \<lbrakk>P \<longrightarrow> Q; Q \<longrightarrow> P\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
     \<sqdot> ccontr:         (\<not>P \<Longrightarrow> False) \<Longrightarrow> P
     \<sqdot> classical:      (\<not>P \<Longrightarrow> P) \<Longrightarrow> P
     \<sqdot> excluded_middle: \<not>P \<or> P
     \<sqdot> disjCI:         (\<not>Q \<Longrightarrow> P) \<Longrightarrow> P \<or> Q
     \<sqdot> impCE:          \<lbrakk>P \<longrightarrow> Q; \<not>P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
     \<sqdot> iffCE:          \<lbrakk>P = Q; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R; \<lbrakk>\<not>P; \<not>Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
     \<sqdot> swap:           \<lbrakk>\<not>P; \<not>R \<Longrightarrow> P\<rbrakk> \<Longrightarrow> R
\<close>

text \<open>
   Resumen de reglas de cuantificadores:
   \<sqdot> allE:    \<lbrakk>\<forall>x. P x; P y \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
   \<sqdot> allI:    (\<And>x. P x) \<Longrightarrow> \<forall>x. P x

   \<sqdot> exI:     P a \<Longrightarrow> \<exists>x. P x
   \<sqdot> exE:     \<lbrakk>\<exists>x. P x;\<And>x. P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q

\<close>

text \<open>
   Resumen de reglas de la igualdad:
   \<sqdot> refl:       t = t
   \<sqdot> subst:      \<lbrakk>s = t; P s\<rbrakk> \<Longrightarrow> P t
   \<sqdot> trans:      \<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t
   \<sqdot> sym:        s = t \<Longrightarrow> t = s
   \<sqdot> not_sym:    t \<noteq> s \<Longrightarrow> s \<noteq> t
   \<sqdot> ssubst:     \<lbrakk>t = s; P s\<rbrakk> \<Longrightarrow> P t
   \<sqdot> box_equals: \<lbrakk>a = b; a = c; b = d\<rbrakk> \<Longrightarrow> c = d
   \<sqdot> arg_cong:   x = y \<Longrightarrow> f x = f y
   \<sqdot> fun_cong:   f = g \<Longrightarrow> f x = g x
   \<sqdot> cong:       \<lbrakk>f = g; x = y\<rbrakk> \<Longrightarrow> f x = g y
\<close>

text \<open>
   Nota: Más información sobre las reglas de inferencia se encuentra en
   la sección 2.2 de "Isabelle's Logics: HOL" http://goo.gl/ZwdUu
   (página 8).
\<close>

end
