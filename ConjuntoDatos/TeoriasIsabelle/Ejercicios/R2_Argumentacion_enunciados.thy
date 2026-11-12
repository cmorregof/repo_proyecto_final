(* Argumentación proposicional --- enunciados para el estudiante.
   Fuente: Alonso (2018), capitulo 3. CC BY-NC-SA. *)

theory R2_Argumentacion_enunciados
imports Main
begin

chapter \<open>Argumentación proposicional --- enunciados\<close>

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
  Ejercicio 1. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si no está el mañana ni el ayer escrito, entonces no está el mañana
     escrito.
  Usar M: El mañana está escrito.
       A: El ayer está escrito.
   \<close>
lemma ejercicio_1:
  "\<not>M \<and> \<not>A \<Longrightarrow> \<not>M"
oops


text \<open> 
  Ejercicio 2. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Siempre que un número x es divisible por 10, acaba en 0. El número
     x no acaba en 0. Por lo tanto, x no es divisible por 10.
  Usar D para "el número es divisible por 10" y
       C para "el número acaba en cero".
   \<close>
lemma ejercicio_2:
  "\<lbrakk>C \<longrightarrow> D; \<not>D\<rbrakk> \<Longrightarrow> \<not>C"
oops


text \<open> 
  Ejercicio 3. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si no hay control de nacimientos, entonces la población crece
     ilimitadamente; pero si la población crece ilimitadamente,
     aumentará el índice de pobreza. Por consiguiente, si no hay control
     de nacimientos, aumentará el índice de pobreza.
  Usar N: Hay control de nacimientos.
       P: La población crece ilimitadamente,
       I: Aumentará el índice de pobreza.
   \<close>
lemma ejercicio_3:
  "\<lbrakk>\<not>N \<longrightarrow> P; P \<longrightarrow> I\<rbrakk> \<Longrightarrow> \<not>N \<longrightarrow> I"
oops


text \<open> 
  Ejercicio 4. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si te llamé por teléfono, entonces recibiste mi llamada y no es
     cierto que no te avisé del peligro que corrías. Por consiguiente,
     como te llamé, es cierto que te avisé del peligro que corrías.
  Usar T: Te llamé por teléfono.
       R: Recibiste mi llamada.
       P: Te avisé del peligro que corrías.
   \<close>
lemma ejercicio_4:
  "T \<longrightarrow> R \<and> \<not>\<not>A \<Longrightarrow> T \<longrightarrow> A"
oops


text \<open> 
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
   \<close>
lemma ejercicio_5:
  "\<lbrakk>A \<or> P \<longrightarrow> R \<and> F; F \<or> N \<longrightarrow> Or\<rbrakk> \<Longrightarrow> A \<longrightarrow> Or"
oops


text \<open> 
  Ejercicio 6. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Cuando tanto la temperatura como la presión atmosférica permanecen
     contantes, no llueve. La temperatura permanece constante. Por lo
     tanto, en caso de que llueva, la presión atmosférica no permanece
     constante.
  Usar T para "La temperatura permanece constante",
       P para "La presión atmosférica permanece constante" y
       L para "Llueve".
   \<close>
lemma ejercicio_6:
  "\<lbrakk>T \<and> P \<longrightarrow> \<not>L; T\<rbrakk> \<Longrightarrow> L \<longrightarrow> \<not>P"
oops


text \<open> 
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
   \<close>
lemma ejercicio_7:
  "\<lbrakk>(L \<longrightarrow> Ob) \<and> (I \<longrightarrow> C); \<not>Ob \<or> \<not>C\<rbrakk> \<Longrightarrow> \<not>L \<or> \<not>I"
oops


text \<open> 
  Ejercicio 8. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Me matan si no trabajo y si trabajo me matan. Me matan siempre me
     matan.
  Usar M: Me matan.
       T: Trabajo.
   \<close>
lemma ejercicio_8:
  "(\<not>T \<longrightarrow> M) \<and> (T \<longrightarrow> M) \<Longrightarrow> M"
oops


text \<open> 
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
   \<close>
lemma ejercicio_9:
  assumes "A \<longrightarrow> (M \<longleftrightarrow> \<not>B)"
          "A \<or> B"
  shows   "\<not>B \<longrightarrow> M"
oops


text \<open> 
  Ejercicio 10. Formalizar, y demostrar la corrección, del siguiente
  argumento
     Si trabajo gano dinero, pero si no trabajo gozo de la vida. Sin
     embargo, si trabajo no gozo de la vida, mientras que si no trabajo
     no gano dinero. Por lo tanto, gozo de la vida si y sólo si no gano
  dinero.
  Usar p: Trabajo
       q: Gano dinero.
       r: Gozo de la vida.
   \<close>
lemma ejercicio_61:
  "\<lbrakk>(p \<longrightarrow> q) \<and> (\<not>p \<longrightarrow> r); (p \<longrightarrow> \<not>r) \<and> (\<not>p \<longrightarrow> \<not>q)\<rbrakk> \<Longrightarrow> r \<longleftrightarrow> \<not>q"
oops


text \<open> 
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
   \<close>
lemma ejercicio_11:
  "\<lbrakk>C \<and> Q \<longrightarrow> P; (\<not>C \<longrightarrow> \<not>Om) \<and> (\<not>Q \<longrightarrow> M); \<not>P; E \<longrightarrow> Om \<and> \<not>M\<rbrakk> \<Longrightarrow> \<not>E"
oops

end
