(* Argumentación proposicional --- soluciones
   Relacion de ejercicios del capitulo 3 de: Jose A. Alonso
   Jimenez, Demostracion asistida por ordenador con Isabelle/HOL,
   Universidad de Sevilla, 2018. Licencia CC BY-NC-SA.
   Portado a Isabelle2025-2. *)

theory R2_Argumentacion
imports Main
begin

text \<open>
  ---------------------------------------------------------------------
  El objetivo de esta es relación formalizar y demostrar la corrección
  de los argumentos usando sólo las reglas básicas de deducción natural
  de la lógica proposicional (sin usar el método auto).

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
     ---------------------------------------------------------------------
\<close>

text \<open>
  Se usarán las reglas notnotI y mt que demostramos a continuación.
  \<close>

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
by auto

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto

text \<open> ---------------------------------------------------------------
  Ejercicio 1. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si no está el mañana ni el ayer escrito, entonces no está el mañana
     escrito.
  Usar M: El mañana está escrito.

       A: El ayer está escrito.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es:\<close>
lemma ejercicio_1_1:
  "\<not>M \<and> \<not>A \<Longrightarrow> \<not>M"
by auto

text \<open>La demostración estructurada es:\<close>
lemma ejercicio_1_2:
  assumes "\<not>M \<and> \<not>A"
  shows   "\<not>M"
using assms ..

text \<open>La demostración detallada es:\<close>
lemma ejercicio_1_3:
  assumes "\<not>M \<and> \<not>A"
  shows   "\<not>M"
using assms by (rule conjunct1)

text \<open> ---------------------------------------------------------------
  Ejercicio 2. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Siempre que un número x es divisible por 10, acaba en 0. El número
     x no acaba en 0. Por lo tanto, x no es divisible por 10.
  Usar D para "el número es divisible por 10" y
       C para "el número acaba en cero".
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_2_1:
  "\<lbrakk>C \<longrightarrow> D; \<not>D\<rbrakk> \<Longrightarrow> \<not>C"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_2_2:
  assumes "C \<longrightarrow> D"
          "\<not>D"
  shows   "\<not>C"
proof
  assume "C"
  with assms(1) have "D" ..
  with assms(2) show False ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_2_3:
  assumes "C \<longrightarrow> D"
          "\<not>D"
  shows   "\<not>C"
proof
  assume "C"
  with assms(1) have "D" by (rule mp)
  with assms(2) show False by (rule notE)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 3. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si no hay control de nacimientos, entonces la población crece
     ilimitadamente; pero si la población crece ilimitadamente,
     aumentará el índice de pobreza. Por consiguiente, si no hay control
     de nacimientos, aumentará el índice de pobreza.
  Usar N: Hay control de nacimientos.
       P: La población crece ilimitadamente,
       I: Aumentará el índice de pobreza.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_3_1:
  "\<lbrakk>\<not>N \<longrightarrow> P; P \<longrightarrow> I\<rbrakk> \<Longrightarrow> \<not>N \<longrightarrow> I"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_3_2:
  assumes "\<not>N \<longrightarrow> P"
          "P \<longrightarrow> I"
  shows   "\<not>N \<longrightarrow> I"
proof
  assume "\<not>N"
  with assms(1) have "P" ..
  with assms(2) show "I" ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_3_3:
  assumes "\<not>N \<longrightarrow> P"
          "P \<longrightarrow> I"
  shows   "\<not>N \<longrightarrow> I"
proof (rule impI)

  assume "\<not>N"
  with assms(1) have "P" by (rule mp)
  with assms(2) show "I" by (rule mp)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 4. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si te llamé por teléfono, entonces recibiste mi llamada y no es
     cierto que no te avisé del peligro que corrías. Por consiguiente,
     como te llamé, es cierto que te avisé del peligro que corrías.
  Usar T: Te llamé por teléfono.
       R: Recibiste mi llamada.
       P: Te avisé del peligro que corrías.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es:\<close>
lemma ejercicio_4_1:
  "T \<longrightarrow> R \<and> \<not>\<not>A \<Longrightarrow> T \<longrightarrow> A"
by auto

text \<open>La demostración estructurada es:\<close>
lemma ejercicio_4_2:
  assumes "T \<longrightarrow> R \<and> \<not>\<not>A"
  shows   "T \<longrightarrow> A"
proof
  assume "T"
  with assms have "R \<and> \<not>\<not>A" ..
  hence "\<not>\<not>A" ..
  thus "A" by (rule notnotD)
qed

text \<open>La demostración detallada es:\<close>
lemma ejercicio_4_3:
  assumes "T \<longrightarrow> R \<and> \<not>\<not>A"
  shows   "T \<longrightarrow> A"
proof (rule impI)
  assume "T"
  with assms(1) have "R \<and> \<not>\<not>A" by (rule mp)
  hence "\<not>\<not>A" by (rule conjunct2)
  thus "A" by (rule notnotD)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 5. Formalizar, y demostrar la corrección, del siguiente

  argumento
     Si la válvula está abierta o la monitorización está preparada,
     entonces se envía una señal de reconocimiento y un mensaje de
     funcionamiento al controlador del ordenador. Si se envía un mensaje
     de funcionamiento al controlador del ordenador o el sistema está en
     estado normal, entonces se aceptan las órdenes del operador. Por lo
     tanto, si la válvula está abierta, entonces se aceptan las órdenes
     del operador.
  Usar A : La válvula está abierta.
       P : La monitorización está preparada.
       R : Envía una señal de reconocimiento.
       F : Envía un mensaje de funcionamiento.
       N : El sistema está en estado normal.
       O : Se aceptan órdenes del operador.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_5_1:
  "\<lbrakk>A \<or> P \<longrightarrow> R \<and> F; F \<or> N \<longrightarrow> Or\<rbrakk> \<Longrightarrow> A \<longrightarrow> Or"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_5_2:
  assumes "A \<or> P \<longrightarrow> R \<and> F"
          "F \<or> N \<longrightarrow> Or"
  shows   "A \<longrightarrow> Or"
proof
  assume "A"
  hence "A \<or> P" ..
  with assms(1) have "R \<and> F" ..
  hence "F" ..
  hence "F \<or> N" ..
  with assms(2) show "Or" ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_5_3:
  assumes "A \<or> P \<longrightarrow> R \<and> F"
          "F \<or> N \<longrightarrow> Or"
  shows   "A \<longrightarrow> Or"
proof (rule impI)
  assume "A"
  hence "A \<or> P" by (rule disjI1)
  with assms(1) have "R \<and> F" by (rule mp)
  hence "F" by (rule conjunct2)

  hence "F \<or> N" by (rule disjI1)
  with assms(2) show "Or" by (rule mp)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 6. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Cuando tanto la temperatura como la presión atmosférica permanecen
     contantes, no llueve. La temperatura permanece constante. Por lo
     tanto, en caso de que llueva, la presión atmosférica no permanece
     constante.
  Usar T para "La temperatura permanece constante",
       P para "La presión atmosférica permanece constante" y
       L para "Llueve".
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_6_1:
  "\<lbrakk>T \<and> P \<longrightarrow> \<not>L; T\<rbrakk> \<Longrightarrow> L \<longrightarrow> \<not>P"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_6_2:
  assumes "T \<and> P \<longrightarrow> \<not>L"
          "T"
  shows   "L \<longrightarrow> \<not>P"
proof
  assume "L"
  show "\<not>P"
  proof
    assume "P"
    with `T` have "T \<and> P" ..
    with assms(1) have "\<not>L" ..
    thus "False" using `L` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_6_3:
  assumes "T \<and> P \<longrightarrow> \<not>L"
          "T"
  shows   "L \<longrightarrow> \<not>P"
proof (rule impI)
  assume "L"
  show "\<not>P"

  proof
    assume "P"
    with `T` have "T \<and> P" by (rule conjI)
    with assms(1) have "\<not>L" by (rule mp)
    thus "False" using `L` by (rule notE)
  qed
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 7. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si el general era leal, hubiera obedecido las órdenes, y si era
     inteligente las hubiera comprendido. O el general desobedeció las
     órdenes o no las comprendió. Luego, el general era desleal o no era
     inteligente.
  Usar L: El general es leal.
       Ob: El general obedece las órdenes.
       I: El general es inteligente.
       C: El general comprende las órdenes.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_7_1:
  "\<lbrakk>(L \<longrightarrow> Ob) \<and> (I \<longrightarrow> C); \<not>Ob \<or> \<not>C\<rbrakk> \<Longrightarrow> \<not>L \<or> \<not>I"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_7_2:
  assumes "(L \<longrightarrow> Ob) \<and> (I \<longrightarrow> C)"
          "\<not>Ob \<or> \<not>C"
  shows   "\<not>L \<or> \<not>I"
using assms(2)
proof
  assume "\<not>Ob"
  have "L \<longrightarrow> Ob" using assms(1) ..
  hence "\<not>L" using `\<not>Ob` by (rule mt)
  thus "\<not>L \<or> \<not>I" ..
next
  assume "\<not>C"
  have "I \<longrightarrow> C" using assms(1) ..
  hence "\<not>I" using `\<not>C` by (rule mt)
  thus "\<not>L \<or> \<not>I" ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_7_3:
  assumes "(L \<longrightarrow> Ob) \<and> (I \<longrightarrow> C)"
          "\<not>Ob \<or> \<not>C"
  shows   "\<not>L \<or> \<not>I"
using assms(2)
proof (rule disjE)
  assume "\<not>Ob"
  have "L \<longrightarrow> Ob" using assms(1) by (rule conjunct1)
  hence "\<not>L" using `\<not>Ob` by (rule mt)
  thus "\<not>L \<or> \<not>I" by (rule disjI1)
next
  assume "\<not>C"
  have "I \<longrightarrow> C" using assms(1) by (rule conjunct2)
  hence "\<not>I" using `\<not>C` by (rule mt)
  thus "\<not>L \<or> \<not>I" by (rule disjI2)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 8. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Me matan si no trabajo y si trabajo me matan. Me matan siempre me
     matan.
  Usar M: Me matan.
       T: Trabajo.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_8_1:
  "(\<not>T \<longrightarrow> M) \<and> (T \<longrightarrow> M) \<Longrightarrow> M"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_8_2:
  assumes "(\<not>T \<longrightarrow> M) \<and> (T \<longrightarrow> M)"
  shows    "M"
proof -
  have "\<not>T \<or> T" ..
  thus "M"
  proof
    assume "\<not>T"
    have "\<not>T \<longrightarrow> M" using assms ..
    thus "M" using `\<not>T` ..
  next
    assume "T"
    have "T \<longrightarrow> M" using assms ..

    thus "M" using `T` ..
  qed
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_8_3:
  assumes "(\<not>T \<longrightarrow> M) \<and> (T \<longrightarrow> M)"
  shows    "M"
proof -
  have "\<not>T \<or> T" by (rule excluded_middle)
  thus "M"
  proof (rule disjE)
    assume "\<not>T"
    have "\<not>T \<longrightarrow> M" using assms by (rule conjunct1)
    thus "M" using `\<not>T` by (rule mp)
  next
    assume "T"
    have "T \<longrightarrow> M" using assms by (rule conjunct2)
    thus "M" using `T` by (rule mp)
  qed
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 9. Formalizar, y demostrar la corrección, del siguiente
  argumento
     En cierto experimento, cuando hemos empleado un fármaco A, el
     paciente ha mejorado considerablemente en el caso, y sólo en el
     caso, en que no se haya empleado también un fármaco B. Además, o se
     ha empleado el fármaco A o se ha empleado el fármaco B. En
     consecuencia, podemos afirmar que si no hemos empleado el fármaco
     B, el paciente ha mejorado considerablemente.
  Usar A: Hemos empleado el fármaco A.
       B: Hemos empleado el fármaco B.
       M: El paciente ha mejorado notablemente.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_9_1:
  assumes "A \<longrightarrow> (M \<longleftrightarrow> \<not>B)"
          "A \<or> B"
  shows   "\<not>B \<longrightarrow> M"
using assms
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_9_2:
  assumes "A \<longrightarrow> (M \<longleftrightarrow> \<not>B)"
          "A \<or> B"
  shows   "\<not>B \<longrightarrow> M"
proof
  assume "\<not>B"
  note `A \<or> B`
  hence "A"
  proof
    assume "A"
    thus "A" .
  next
    assume "B"
    with `\<not>B` show "A" ..
  qed
  have "M \<longleftrightarrow> \<not>B" using assms(1) `A` ..
  thus "M" using `\<not>B` ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_9_3:
  assumes "A \<longrightarrow> (M \<longleftrightarrow> \<not>B)"
          "A \<or> B"
  shows   "\<not>B \<longrightarrow> M"
proof (rule impI)
  assume "\<not>B"
  note `A \<or> B`
  hence "A"
  proof (rule disjE)
    assume "A"
    thus "A" by this
  next
    assume "B"
    with `\<not>B` show "A" by (rule notE)
  qed
  have "M \<longleftrightarrow> \<not>B" using assms(1) `A` by (rule mp)
  thus "M" using `\<not>B` by (rule iffD2)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 10. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si trabajo gano dinero, pero si no trabajo gozo de la vida. Sin
     embargo, si trabajo no gozo de la vida, mientras que si no trabajo
     no gano dinero. Por lo tanto, gozo de la vida si y sólo si no gano

  dinero.
  Usar p: Trabajo
       q: Gano dinero.
       r: Gozo de la vida.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_61_1:
  "\<lbrakk>(p \<longrightarrow> q) \<and> (\<not>p \<longrightarrow> r); (p \<longrightarrow> \<not>r) \<and> (\<not>p \<longrightarrow> \<not>q)\<rbrakk> \<Longrightarrow> r \<longleftrightarrow> \<not>q"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_61_2:
  assumes "(p \<longrightarrow> q) \<and> (\<not>p \<longrightarrow> r)"
          "(p \<longrightarrow> \<not>r) \<and> (\<not>p \<longrightarrow> \<not>q)"
  shows   "r \<longleftrightarrow> \<not>q"
proof
  assume "r"
  hence "\<not>\<not>r" by (rule notnotI)
  have "p \<longrightarrow> \<not>r" using assms(2) ..
  hence "\<not>p" using `\<not>\<not>r` by (rule mt)
  have "\<not>p \<longrightarrow> \<not>q" using assms(2) ..
  thus "\<not>q" using `\<not>p` ..
next
  assume "\<not>q"
  have "p \<longrightarrow> q" using assms(1) ..
  hence "\<not>p" using `\<not>q` by (rule mt)
  have "\<not>p \<longrightarrow> r" using assms(1) ..
  thus "r" using `\<not>p` ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_61_3:
  assumes "(p \<longrightarrow> q) \<and> (\<not>p \<longrightarrow> r)"
          "(p \<longrightarrow> \<not>r) \<and> (\<not>p \<longrightarrow> \<not>q)"
  shows   "r \<longleftrightarrow> \<not>q"
proof (rule iffI)
  assume "r"
  hence "\<not>\<not>r" by (rule notnotI)
  have "p \<longrightarrow> \<not>r" using assms(2) by (rule conjunct1)
  hence "\<not>p" using `\<not>\<not>r` by (rule mt)
  have "\<not>p \<longrightarrow> \<not>q" using assms(2) by (rule conjunct2)
  thus "\<not>q" using `\<not>p` by (rule mp)
next
  assume "\<not>q"

  have "p \<longrightarrow> q" using assms(1) by (rule conjunct1)
  hence "\<not>p" using `\<not>q` by (rule mt)
  have "\<not>p \<longrightarrow> r" using assms(1) by (rule conjunct2)
  thus "r" using `\<not>p` by (rule mp)
qed

text \<open> ---------------------------------------------------------------
  Ejercicio 11. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si Dios fuera capaz de evitar el mal y quisiera hacerlo, lo
     haría. Si Dios fuera incapaz de evitar el mal, no sería
     omnipotente; si no quisiera evitar el mal sería malévolo. Dios no
     evita el mal. Si Dios existe, es omnipotente y no es
     malévolo. Luego, Dios no existe.
  Usar C: Dios es capaz de evitar el mal.
       Q: Dios quiere evitar el mal.
       Om: Dios es omnipotente.
       M: Dios es malévolo.
       P: Dios evita el mal.
       E: Dios existe.
  ------------------------------------------------------------------ \<close>

text \<open>La demostración automática es\<close>
lemma ejercicio_11_1:
  "\<lbrakk>C \<and> Q \<longrightarrow> P; (\<not>C \<longrightarrow> \<not>Om) \<and> (\<not>Q \<longrightarrow> M); \<not>P; E \<longrightarrow> Om \<and> \<not>M\<rbrakk> \<Longrightarrow> \<not>E"
by auto

text \<open>La demostración estructurada es\<close>
lemma ejercicio_11_2:
  assumes "C \<and> Q \<longrightarrow> P"
          "(\<not>C \<longrightarrow> \<not>Om) \<and> (\<not>Q \<longrightarrow> M)"
          "\<not>P"
          "E \<longrightarrow> Om \<and> \<not>M"
  shows   "\<not>E"
proof
  assume "E"
  have "Om \<and> \<not>M" using assms(4) `E` ..
  hence "Om" ..
  hence "\<not>\<not>Om" by (rule notnotI)
  have "\<not>C \<longrightarrow> \<not>Om" using assms(2) ..
  hence "\<not>\<not>C" using `\<not>\<not>Om` by (rule mt)
  hence "C" by (rule notnotD)
  have "\<not>M" using `Om \<and> \<not>M` ..
  have "\<not>Q \<longrightarrow> M" using assms(2) ..
  hence "\<not>\<not>Q" using `\<not>M` by (rule mt)

  hence "Q" by (rule notnotD)
  with `C` have "C \<and> Q" ..
  with assms(1) have "P" ..
  with assms(3) show False ..
qed

text \<open>La demostración detallada es\<close>
lemma ejercicio_11_3:
  assumes "C \<and> Q \<longrightarrow> P"
          "(\<not>C \<longrightarrow> \<not>Om) \<and> (\<not>Q \<longrightarrow> M)"
          "\<not>P"
          "E \<longrightarrow> Om \<and> \<not>M"
  shows   "\<not>E"
proof (rule notI)
  assume "E"
  with assms(4) have "Om \<and> \<not>M" by (rule mp)
  hence "Om" by (rule conjunct1)
  hence "\<not>\<not>Om" by (rule notnotI)
  have "\<not>C \<longrightarrow> \<not>Om" using assms(2) by (rule conjunct1)
  hence "\<not>\<not>C" using `\<not>\<not>Om` by (rule mt)
  hence "C" by (rule notnotD)
  have "\<not>M" using `Om \<and> \<not>M` by (rule conjunct2)
  have "\<not>Q \<longrightarrow> M" using assms(2) by (rule conjunct2)
  hence "\<not>\<not>Q" using `\<not>M` by (rule mt)
  hence "Q" by (rule notnotD)
  with `C` have "C \<and> Q" by (rule conjI)
  with assms(1) have "P" by (rule mp)
  with assms(3) show False by (rule notE)
qed

end
