(**  Lógica Computacional 2026-2                                      
    Práctica 11: Introducción a Rocq                                
                                                                    
   Profesor: Manuel Soto Romero                                     
   Ayudante: Diego Mendez Medina                                    
   Lab: Erick Arroyo 
   Equipo: 
    - Joaquin Rodrigo Ramirez Mendoza
    - Dana Ximena Sanchez Loaeza
   *)


(* ################################################################# *)
(** Bloque 1 — Tipos, Check y Compute *)
(* ################################################################# *)

(** Ejercicio 1: Inspeccionando tipos

    Ejecuta cada línea en el scratchpad y anota el tipo que reporta
    Rocq para cada expresión. *)

Check true.
Check false.
Check negb.
Check (negb true).
Check nat.
Check (S (S O)).
Check (1 + 1 = 2).
Check (forall n : nat, n = n).

(** Ejercicio 2: Evaluación con Compute

    Predice el resultado de cada expresión _antes_ de ejecutarla,
    luego verifica con [Compute]. *)
Compute negb (negb true).
Compute andb true false.
Compute orb false false.
Compute 3 + 4.
Compute 10 - 3.
Compute 10 - 15.
Compute 2 * 6.

(* ################################################################# *)
(**  Bloque 2 — Definiciones y Fixpoint *)
(* ################################################################# *)

(** **** Ejercicio 3: Funciones booleanas básicas *)

Definition nandb (b1 b2 : bool) : bool :=
  match b1 with
  | true =>
      match b2 with
      | true => false
      | false => true
      end
  | false => true
  end.

Definition xorb' (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true   => false
  | true, false  => true
  | false, true  => true
  | false, false => false
  end.

Example test_nandb1 : nandb true  false = true.  Proof. reflexivity. Qed.
Example test_nandb2 : nandb false false = true.  Proof. reflexivity. Qed.
Example test_nandb3 : nandb true  true  = false. Proof. reflexivity. Qed.
Example test_xorb1  : xorb' true  false = true.  Proof. reflexivity. Qed.
Example test_xorb2  : xorb' true  true  = false. Proof. reflexivity. Qed.

(** **** Ejercicio 4: Funciones sobre naturales *)

(** [par] ya está definida; no la modifiques. *)
Fixpoint par (n : nat) : bool :=
  match n with
  | O       => true
  | S O     => false
  | S (S k) => par k
  end.

Definition impar (n : nat) : bool :=
  negb (par n).

Fixpoint suma_nat (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (suma_nat n' m)
  end.

Fixpoint mult_nat (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => suma_nat m (mult_nat n' m)
  end.

Compute par 4.        (* Esperado: true  *)
Compute par 7.        (* Esperado: false *)
Compute suma_nat 3 5. (* Esperado: 8     *)
Compute mult_nat 3 4. (* Esperado: 12    *)

(** **** Ejercicio 5: Potencia *)

Fixpoint pot (b e : nat) : nat :=
  match e with
  | O    => S O
  | S k  => mult_nat b (pot b k)
  end.

Example test_pot1 : pot 2 0 = 1. Proof. reflexivity. Qed.
Example test_pot2 : pot 2 3 = 8. Proof. reflexivity. Qed.
Example test_pot3 : pot 3 2 = 9. Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Bloque 3 — Teoremas simples con reflexivity y simpl *)
(* ################################################################# *)

(** **** Ejercicio 6: Demostraciones por evaluación *)

Theorem suma0_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem negb_involutiva : negb (negb true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem andb_comm_ff : andb false false = andb false false.
Proof.
  simpl.
  reflexivity.
Qed.

(* ################################################################# *)
(** * Bloque 4 — Análisis por casos con destruct *)
(* ################################################################# *)

(** **** Ejercicio 7: Booleanos e identidades [()] *)

Theorem negb_negb : forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem orb_true_l : forall b : bool, orb true b = true.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** **** Ejercicio 8: Conmutatividad de orb *)

Theorem orb_comm : forall b1 b2 : bool,
    orb b1 b2 = orb b2 b1.
Proof.
  intros b1 b2.
  destruct b1.
  - (* b1 = true *)
    destruct b2.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - (* b1 = false *)
    destruct b2.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(** **** Ejercicio 9: Casos sobre naturales *)

Theorem par_S_impar : forall n : nat,
    par (S n) = negb (par n).
Proof.
  intros n.
  destruct n as [| n'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    destruct n' as [| k].
    + (* n = 1 *)
      simpl. reflexivity.
    + (* n = S (S k) *)
      simpl. reflexivity.
Qed.

(* ################################################################# *)
(** * Bloque 5 — Reescritura con rewrite *)
(* ################################################################# *)

(** **** Ejercicio 10: Usando hipótesis [()] *)

Theorem reescritura_simple :
    forall n m : nat, n = m -> n + 0 = m + 0.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem reescritura_inv :
    forall n m : nat, m = n -> n + 0 = m + 0.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

(** **** Ejercicio 11: Transitividad de la igualdad a mano *)

Theorem trans_eq_nat :
    forall a b c : nat, a = b -> b = c -> a = c.
Proof.
  intros a b c Hab Hbc.
  rewrite Hab.
  rewrite Hbc.
  reflexivity.
Qed.

(** **** Ejercicio 12: Congruencia y sustitución [()] *)

(** Definición de [suma] del marco teórico — no modificar. *)
Fixpoint suma (n m : nat) : nat :=
  match n with
  | O   => m
  | S k => S (suma k m)
  end.

Theorem congr_S : forall n m : nat, n = m -> S n = S m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem congr_suma :
    forall n m k : nat, n = m -> suma (S n) k = suma (S m) k.
Proof.
  intros n m k H.
  rewrite H.
  reflexivity.
Qed.

(* ################################################################# *)
(** * Bloque 6 — Admitted y Abort *)
(* ################################################################# *)

(** **** Ejercicio 13 *)

(** Parte (a): ejecuta y observa. *)
Theorem ejemplo_admitted : forall n : nat, n + 0 = n.
Proof.
  Admitted.

(** Parte (b): ejecuta y anota la advertencia de la barra lateral. *)
Theorem usa_admitted : forall n : nat, n + 0 + 0 = n.
Proof.
  intro n.
  rewrite ejemplo_admitted.
  rewrite ejemplo_admitted.
  reflexivity.
Qed.

(** Parte (c): descomenta, ejecuta y observa. *)

Theorem intento_fallido : forall b : bool, b = true.
Proof.
  intro b.
  Abort.

Check negb.
(* ################################################################# *)
(** * Bloque 7 — Reto final [(**)] *)
(* ################################################################# *)

(** **** Ejercicio 14: Propiedades de par e impar [(**)] *)

Theorem par_0 : par 0 = true.
Proof. reflexivity. Qed.

Theorem impar_1 : impar 1 = true.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem par_impar_complementarios :
    forall n : nat, impar n = negb (par n).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(** **** Ejercicio 15: Leyes de De Morgan [(**)] *)

(** La demostración de [demorgan_and] se da completa; estúdiala
    antes de escribir la de [demorgan_or]. *)

Theorem demorgan_and :
    forall a b : bool,
      negb (andb a b) = orb (negb a) (negb b).
Proof.
  intros a b.
  destruct a; destruct b; simpl; reflexivity.
Qed.

Theorem demorgan_or :
    forall a b : bool,
      negb (orb a b) = andb (negb a) (negb b).
Proof.
  intros a b.
  destruct a; destruct b; simpl; reflexivity.
Qed.

(** **** Ejercicio 16: Función de comparación [(**)] *)

(** Tipo y función ya definidos — no modificar. *)
Inductive comparacion : Type :=
  | Eq : comparacion
  | Lt : comparacion
  | Gt : comparacion.

Fixpoint compara (n m : nat) : comparacion :=
  match n, m with
  | O,    O    => Eq
  | O,    S _  => Lt
  | S _,  O    => Gt
  | S n', S m' => compara n' m'
  end.

Theorem compara_refl : forall n : nat, compara n n = Eq.
Proof.
  intros n.
  (* Para probarlo para todo n, al hacer destruct n queda el caso
     n = S n' con objetivo: compara n' n' = Eq, que es el mismo teorema
     pero para n'. Eso requiere inducción pero no está permitido
     o un lema previo equivalente ya demostrado. *)
Admitted.

Theorem compara_0_n : forall n : nat, compara 0 (S n) = Lt.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.