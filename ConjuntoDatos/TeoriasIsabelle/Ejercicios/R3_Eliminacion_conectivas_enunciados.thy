(* Eliminación de conectivas --- enunciados para el estudiante.
   Fuente: Alonso (2018), capitulo 3. CC BY-NC-SA. *)

theory R3_Eliminacion_conectivas_enunciados
imports Main
begin

chapter \<open>Eliminación de conectivas --- enunciados\<close>

text \<open>
  Demuestre cada lema usando solo las reglas basicas de deduccion
  natural. Sustituya cada \<open>oops\<close> por su demostracion.
\<close>


text \<open> 
  Ejercicio 1. Definir \<longleftrightarrow> usando \<and> y \<longrightarrow>; es decir, sustituir en
      (A \<longleftrightarrow> B) = indefinida
  la indefinida por una fórmula que sólo usa las conectivas \<and> y \<longleftrightarrow> y
  demostrar la equivalencia.
   \<close>
lemma bicondicional: "
  (A \<longleftrightarrow> B) = undefined"
oops


text \<open> 
  Ejercicio 2. Definir \<not> usando \<longrightarrow> y False; es decir, sustituir en
      (\<not>A) = indefinida
  la indefinida por una fórmula que sólo usa las conectivas \<longrightarrow> y False
  y demostrar la equivalencia.
   \<close>
lemma negacion:
  "(\<not>A) = undefined"
oops


text \<open> 
  Ejercicio 3. Definir \<or> usando \<longrightarrow> y False; es decir, sustituir en
      (A \<or> B) = indefinida
  la indefinida por una fórmula que sólo usa las conectivas \<longrightarrow> y False
  y demostrar la equivalencia.
   \<close>
lemma disyuncion:
  "(A \<or> B) = undefined"
oops


text \<open> 
  Ejercicio 4. Encontrar una fórmula equivalente a
     (A \<or> (B \<and> C)) \<longleftrightarrow> A
  que sólo use las conectivas False, \<and> y \<longrightarrow> y demostrar la
  equivalencia.
   \<close>
end
