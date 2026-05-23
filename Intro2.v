(**  Lógica Computacional 2026-2                                      
    Práctica 11: Introducción a Rocq                                
                                                                    
   Profesor: Manuel Soto Romero                                     
   Ayudante: Diego Mendez Medina                                    
   Lab: Erick Arroyo 
   Equipo: *)


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
  negb (andb b1 b2).

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
  | O    => m
  | S k  => S (suma_nat k m)
  end.

Fixpoint mult_nat (n m : nat) : nat :=
  match n with
  | O    => O
  | S k  => suma_nat m (mult_nat k m)
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
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem negb_involutiva : negb (negb true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem andb_comm_ff : andb false false = andb false fal
