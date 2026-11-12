(* Eliminación de conectivas --- soluciones
   Relacion de ejercicios del capitulo 3 de: Jose A. Alonso
   Jimenez, Demostracion asistida por ordenador con Isabelle/HOL,
   Universidad de Sevilla, 2018. Licencia CC BY-NC-SA.
   Portado a Isabelle2025-2. *)

theory R3_Eliminacion_conectivas
imports Main
begin

text \<open>
  ---------------------------------------------------------------------
  El objetivo de esta es relación es demostrar cómo a partir de las
  conectivas False, \<and> y \<longrightarrow> pueden definirse las restantes.

     ---------------------------------------------------------------------
\<close>

text \<open> ---------------------------------------------------------------
  Ejercicio 1. Definir \<longleftrightarrow> usando \<and> y \<longrightarrow>; es decir, sustituir en
      (A \<longleftrightarrow> B) = indefinida
  la indefinida por una fórmula que sólo usa las conectivas \<and> y \<longleftrightarrow> y
  demostrar la equivalencia.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma bicondicional: "
  (A \<longleftrightarrow> B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
by auto

text \<open>La demostración estructurada es\<close>
lemma bicondicional_2: "
  (A \<longleftrightarrow> B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
proof
  assume "A \<longleftrightarrow> B"
  show "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  proof
     show "A \<longrightarrow> B"
     proof
       assume "A"
       with `A \<longleftrightarrow> B` show "B" ..
     qed
  next
     show "B \<longrightarrow> A"
     proof
       assume "B"
       with `A \<longleftrightarrow> B` show "A" ..
     qed
  qed
next
  assume 1: "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  show "A \<longleftrightarrow> B"
  proof
     assume "A"
     have "A \<longrightarrow> B"using 1 ..
     thus "B" using `A` ..
  next
     assume "B"
     have "B \<longrightarrow> A"using 1 ..

    thus "A" using `B` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma bicondicional_3: "
  (A \<longleftrightarrow> B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
proof (rule iffI)
  assume "A \<longleftrightarrow> B"
  show "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  proof (rule conjI)
     show "A \<longrightarrow> B"
     proof (rule impI)
       assume "A"
       with `A \<longleftrightarrow> B` show "B" by (rule iffD1)
     qed
  next
     show "B \<longrightarrow> A"
     proof (rule impI)
       assume "B"
       with `A \<longleftrightarrow> B` show "A" by (rule iffD2)
     qed
  qed
next
  assume 1: "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  show "A \<longleftrightarrow> B"
  proof (rule iffI)
     assume "A"
     have "A \<longrightarrow> B"using 1 by (rule conjunct1)
     thus "B" using `A` by (rule mp)
  next
     assume "B"
     have "B \<longrightarrow> A"using 1 by (rule conjunct2)
     thus "A" using `B` by (rule mp)
  qed
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 2. Definir \<not> usando \<longrightarrow> y False; es decir, sustituir en
      (\<not>A) = indefinida
  la indefinida por una fórmula que sólo usa las conectivas \<longrightarrow> y False
  y demostrar la equivalencia.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma negacion:
  "(\<not>A) = (A \<longrightarrow> False)"
by auto

text \<open>La demostración estructurada es\<close>
lemma negacion_2:
  "(\<not>A) = (A \<longrightarrow> False)"
proof
  assume "\<not>A"
  show "A \<longrightarrow> False"
  proof
     assume "A"
     with `\<not>A` show False ..
  qed
next
  assume "A \<longrightarrow> False"
  show "\<not>A"
  proof
     assume "A"
     with `A \<longrightarrow> False` show False ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma negacion_3:
  "(\<not>A) = (A \<longrightarrow> False)"
proof (rule iffI)
  assume "\<not>A"
  show "A \<longrightarrow> False"
  proof (rule impI)
     assume "A"
     with `\<not>A` show False by (rule notE)
  qed
next
  assume "A \<longrightarrow> False"
  show "\<not>A"
  proof (rule notI)
     assume "A"
     with `A \<longrightarrow> False` show False by (rule mp)
  qed
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 3. Definir \<or> usando \<longrightarrow> y False; es decir, sustituir en
      (A \<or> B) = indefinida

  la indefinida por una fórmula que sólo usa las conectivas \<longrightarrow> y False
  y demostrar la equivalencia.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma disyuncion:
  "(A \<or> B) = ((A \<longrightarrow> False) \<longrightarrow> B)"
by auto

text \<open>La demostración estructurada es\<close>
lemma disyuncion_2:
  "(A \<or> B) = ((A \<longrightarrow> False) \<longrightarrow> B)"
proof
  assume "A \<or> B"
  show "(A \<longrightarrow> False) \<longrightarrow> B"
  proof
     assume "A \<longrightarrow> False"
     note `A \<or> B`
     thus "B"
     proof
       assume "A"
       with `A \<longrightarrow> False` have False ..
       thus "B" ..
     next
       assume "B"
       thus "B" .
     qed
  qed
next
  assume "(A \<longrightarrow> False) \<longrightarrow> B"
  show "A \<or> B"
  proof -
     have "\<not>A \<or> A" ..
     thus "A \<or> B"
     proof
       assume "\<not>A"
       have "A \<longrightarrow> False"
       proof
          assume "A"
          with `\<not>A` show False ..
       qed
       with `(A \<longrightarrow> False) \<longrightarrow> B` have "B" ..
       thus "A \<or> B" ..
     next
       assume "A"

      thus "A \<or> B" ..
    qed
  qed
qed

text \<open>La demostración detallada es\<close>
lemma disyuncion_3:
  "(A \<or> B) = ((A \<longrightarrow> False) \<longrightarrow> B)"
proof (rule iffI)
  assume "A \<or> B"
  show "(A \<longrightarrow> False) \<longrightarrow> B"
  proof (rule impI)
     assume "A \<longrightarrow> False"
     note `A \<or> B`
     thus "B"
     proof (rule disjE)
       assume "A"
       with `A \<longrightarrow> False` have False by (rule mp)
       thus "B" by (rule FalseE)
     next
       assume "B"
       thus "B" by this
     qed
  qed
next
  assume "(A \<longrightarrow> False) \<longrightarrow> B"
  show "A \<or> B"
  proof -
     have "\<not>A \<or> A" by (rule excluded_middle)
     thus "A \<or> B"
     proof (rule disjE)
       assume "\<not>A"
       have "A \<longrightarrow> False"
       proof (rule impI)
          assume "A"
          with `\<not>A` show False by (rule notE)
       qed
       with `(A \<longrightarrow> False) \<longrightarrow> B` have "B" by (rule mp)
       thus "A \<or> B" by (rule disjI2)
     next
       assume "A"
       thus "A \<or> B" by (rule disjI1)
     qed
  qed
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 4. Encontrar una fórmula equivalente a
     (A \<or> (B \<and> C)) \<longleftrightarrow> A
  que sólo use las conectivas False, \<and> y \<longrightarrow> y demostrar la
  equivalencia.
  ------------------------------------------------------------------ \<close>

text \<open>Se puede buscar la fórmula con\<close>
lemma ejercicio_4a:
  "(A \<or> (B \<and> C)) \<longleftrightarrow> A"
apply (simp only: bicondicional disyuncion)
oops

text \<open>La fórmula obtenida es\<close>
text \<open>(((A \<longrightarrow> False) \<longrightarrow> B \<and> C) \<longrightarrow> A) \<and> (A \<longrightarrow> (A \<longrightarrow> False) \<longrightarrow> B \<and> C)\<close>
text \<open>La demostración de la equivalencia es\<close>
lemma ejercicio_4b:
  "((A \<or> (B \<and> C)) \<longleftrightarrow> A) \<longleftrightarrow>
   ((((A \<longrightarrow> False) \<longrightarrow> B \<and> C) \<longrightarrow> A) \<and> (A \<longrightarrow> (A \<longrightarrow> False) \<longrightarrow> B \<and> C))"
by (auto simp add: bicondicional disyuncion)

end
