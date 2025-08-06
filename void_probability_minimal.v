(******************************************************************************)
(* void_probability_minimal.v                                                 *)
(* Probabilities with proper budget awareness                                 *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import void_finite_minimal.

Module Void_Probability_Minimal.

(******************************************************************************)
(* FINITE PROBABILITIES AS SIMPLE PAIRS                                      *)
(******************************************************************************)

(* A probability is just a pair of Fin values *)
Definition FinProb := (Fin * Fin)%type.

(* Some concrete probabilities - these are notation, not operations *)
Definition half : FinProb := (fs fz, fs (fs fz)).          (* 1/2 *)
Definition third : FinProb := (fs fz, fs (fs (fs fz))).    (* 1/3 *)

(******************************************************************************)
(* PROBABILITY OPERATIONS - ALL COST BUDGET                                   *)
(******************************************************************************)

(* Probability equality WITH BUDGET *)
Definition prob_eq_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  match fin_eq_b (fst p1) (fst p2) b with
  | (true, b') => 
      fin_eq_b (snd p1) (snd p2) b'
  | (false, b') => (false, b')
  end.

(******************************************************************************)
(* KEY PHILOSOPHICAL POINTS - AS DEFINITIONS                                  *)
(******************************************************************************)

(* No probability has numerator zero - approaching the void *)
Definition avoids_zero (p : FinProb) : Prop :=
  match fst p with
  | fz => False
  | _ => True
  end.

(* For checking avoids_one, we need a specific computation *)
Definition check_avoids_one_half : bool :=
  match half with
  | (fs fz, fs (fs fz)) => true  (* 1 ≠ 2 *)
  | _ => false
  end.

Definition check_avoids_one_third : bool :=
  match third with
  | (fs fz, fs (fs (fs fz))) => true  (* 1 ≠ 3 *)
  | _ => false
  end.

(******************************************************************************)
(* SIMPLE PROVABLE THEOREMS                                                   *)
(******************************************************************************)

(* Our example probabilities avoid zero *)
Theorem half_avoids_zero : avoids_zero half.
Proof.
  unfold avoids_zero, half. simpl.
  exact I.  (* True is trivially provable *)
Qed.

Theorem third_avoids_zero : avoids_zero third.
Proof.
  unfold avoids_zero, third. simpl.
  exact I.
Qed.

(* Direct proofs that our examples avoid one *)
Theorem half_avoids_one : check_avoids_one_half = true.
Proof.
  reflexivity.
Qed.

Theorem third_avoids_one : check_avoids_one_third = true.
Proof.
  reflexivity.
Qed.

(******************************************************************************)
(* THE PHILOSOPHICAL POINT MADE CONCRETE                                      *)
(******************************************************************************)

(* For specific probabilities, we can check properness directly *)
Definition half_is_proper : Prop :=
  avoids_zero half /\ check_avoids_one_half = true.

Definition third_is_proper : Prop :=
  avoids_zero third /\ check_avoids_one_third = true.

Theorem half_proper : half_is_proper.
Proof.
  split.
  - apply half_avoids_zero.
  - apply half_avoids_one.
Qed.

Theorem third_proper : third_is_proper.
Proof.
  split.
  - apply third_avoids_zero.
  - apply third_avoids_one.
Qed.

(******************************************************************************)
(* ADDITIONAL PROBABILITY OPERATIONS WITH BUDGET                              *)
(******************************************************************************)

(* Check if probability avoids zero - this is free since it's structural *)
Definition check_avoids_zero (p : FinProb) : bool :=
  match fst p with
  | fz => false
  | _ => true
  end.

(* Add two probabilities - with budget *)
Definition add_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match fin_eq_b d1 d2 b with
  | (true, b') =>
      (* Same denominator - just add numerators *)
      match add_fin_b n1 n2 b' with
      | (sum, b'') => ((sum, d1), b'')
      end
  | (false, b') =>
      (* Different denominators - would need cross multiplication *)
      (* For now, return first probability *)
      (p1, b')
  end.

End Void_Probability_Minimal.