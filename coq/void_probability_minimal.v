(******************************************************************************)
(* void_probability_minimal.v                                                 *)
(* Probabilities with heat tracking - fraction arithmetic generates heat!     *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.ZArith.ZArith.
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
Definition quarter : FinProb := (fs fz, fs (fs (fs (fs fz)))).  (* 1/4 *)

(******************************************************************************)
(* PROBABILITY OPERATIONS WITH HEAT                                           *)
(******************************************************************************)

(* Probability equality with heat - checking fractions is work! *)
Definition prob_eq_b3 (p1 p2 : FinProb) (b : Budget) : (Bool3 * Budget * Heat) :=
  match fin_eq_b3 (fst p1) (fst p2) b with
  | (BTrue, b', h1) => 
      match fin_eq_b3 (snd p1) (snd p2) b' with
      | (res, b'', h2) => (res, b'', add_heat h1 h2)
      end
  | (BFalse, b', h) => (BFalse, b', h)
  | (BUnknown, b', h) => (BUnknown, b', h)
  end.

(* Collapse to bool for compatibility *)
Definition prob_eq_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  match prob_eq_b3 p1 p2 b with
  | (res, b', _) => (collapse3 res, b')
  end.

(* Add probabilities with heat - fraction arithmetic is expensive! *)
Definition add_prob_heat (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Heat) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match fin_eq_b3 d1 d2 b with
  | (BTrue, b', h1) =>
      (* Same denominator - just add numerators *)
      match add_fin_b_heat n1 n2 b' with
      | (sum, b'', h2) => ((sum, d1), b'', add_heat h1 h2)
      end
  | (BFalse, b', h1) =>
      (* Different denominators - cross multiplication (expensive!) *)
      match mult_fin_heat n1 d2 b' with
      | (v1, b1, h2) =>
          match mult_fin_heat n2 d1 b1 with
          | (v2, b2, h3) =>
              match add_fin_b_heat v1 v2 b2 with
              | (new_n, b3, h4) =>
                  match mult_fin_heat d1 d2 b3 with
                  | (new_d, b4, h5) =>
                      ((new_n, new_d), b4, 
                       add_heat h1 (add_heat h2 (add_heat h3 (add_heat h4 h5))))
                  end
              end
          end
      end
  | (BUnknown, b', h) =>
      (* Can't determine - return first probability *)
      (p1, b', h)
  end.

(* Multiply probabilities with heat *)
Definition mult_prob_heat (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Heat) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin_heat n1 n2 b with
  | (new_n, b1, h1) =>
      match mult_fin_heat d1 d2 b1 with
      | (new_d, b2, h2) => ((new_n, new_d), b2, add_heat h1 h2)
      end
  end.

(* Subtract probabilities with saturation and heat *)
Definition sub_prob_heat (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget * Heat) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match fin_eq_b3 d1 d2 b with
  | (BTrue, b', h1) =>
      (* Same denominator - subtract numerators *)
      match sub_saturate_b_heat n1 n2 b' with
      | (diff, b'', h2) => ((diff, d1), b'', add_heat h1 h2)
      end
  | (BFalse, b', h1) =>
      (* Different denominators - cross multiplication *)
      match mult_fin_heat n1 d2 b' with
      | (v1, b1, h2) =>
          match mult_fin_heat n2 d1 b1 with
          | (v2, b2, h3) =>
              match sub_saturate_b_heat v1 v2 b2 with
              | (diff_n, b3, h4) =>
                  match mult_fin_heat d1 d2 b3 with
                  | (new_d, b4, h5) =>
                      ((diff_n, new_d), b4,
                       add_heat h1 (add_heat h2 (add_heat h3 (add_heat h4 h5))))
                  end
              end
          end
      end
  | (BUnknown, b', h) => ((fz, fs fz), b', h)  (* Unknown - return 0 *)
  end.

(* Compare probabilities with three-valued result *)
Definition prob_le_b3 (p1 p2 : FinProb) (b : Budget) : (Bool3 * Budget * Heat) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  (* p1 ≤ p2 iff n1*d2 ≤ n2*d1 *)
  match mult_fin_heat n1 d2 b with
  | (v1, b1, h1) =>
      match mult_fin_heat n2 d1 b1 with
      | (v2, b2, h2) =>
          match le_fin_b3 v1 v2 b2 with
          | (res, b3, h3) => (res, b3, add_heat h1 (add_heat h2 h3))
          end
      end
  end.

(******************************************************************************)
(* INTERVAL PROBABILITIES - When exhausted                                   *)
(******************************************************************************)

Inductive ProbInterval :=
  | PExact : FinProb -> ProbInterval
  | PRange : FinProb -> FinProb -> ProbInterval
  | PUnknown : ProbInterval.

(* Return interval when can't compute exactly *)
Definition add_prob_interval (p1 p2 : FinProb) (b : Budget) 
  : (ProbInterval * Budget * Heat) :=
  match b with
  | fz => (PUnknown, fz, fz)
  | fs fz => 
      (* Very low budget - return range *)
      (PRange p1 (fs (fst p1), snd p1), fs fz, fs fz)
  | _ =>
      match add_prob_heat p1 p2 b with
      | (res, b', h) => (PExact res, b', h)
      end
  end.

(******************************************************************************)
(* BACKWARD COMPATIBILITY                                                    *)
(******************************************************************************)

Definition add_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match add_prob_heat p1 p2 b with
  | (res, b', _) => (res, b')
  end.

Definition mult_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match mult_prob_heat p1 p2 b with
  | (res, b', _) => (res, b')
  end.

Definition sub_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match sub_prob_heat p1 p2 b with
  | (res, b', _) => (res, b')
  end.

Definition prob_le_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  match prob_le_b3 p1 p2 b with
  | (res, b', _) => (collapse3 res, b')
  end.

(******************************************************************************)
(* KEY PHILOSOPHICAL POINTS - UNCHANGED                                      *)
(******************************************************************************)

(* No probability has numerator zero - approaching the void *)
Definition avoids_zero (p : FinProb) : Prop :=
  match fst p with
  | fz => False
  | _ => True
  end.

(* Check if probability avoids zero - this is free since it's structural *)
Definition check_avoids_zero (p : FinProb) : bool :=
  match fst p with
  | fz => false
  | _ => true
  end.

(******************************************************************************)
(* HEAT CONSERVATION FOR PROBABILITIES                                       *)
(******************************************************************************)

Axiom prob_heat_conservation_add : forall p1 p2 b b' res h,
  add_prob_heat p1 p2 b = (res, b', h) -> add_heat h b' = b.

Axiom prob_heat_conservation_mult : forall p1 p2 b b' res h,
  mult_prob_heat p1 p2 b = (res, b', h) -> add_heat h b' = b.

(* Fraction arithmetic generates more heat than integer arithmetic *)
Axiom fraction_heat_penalty : forall p1 p2 b res b' h,
  add_prob_heat p1 p2 b = (res, b', h) ->
  exists h_int b_int, 
    add_fin_b_heat (fst p1) (fst p2) b = (fst res, b_int, h_int) /\
    (fin_to_Z_PROOF_ONLY h >= fin_to_Z_PROOF_ONLY h_int)%Z.

(******************************************************************************)
(* THEOREMS - Previous ones still hold                                       *)
(******************************************************************************)

Theorem half_avoids_zero : avoids_zero half.
Proof. unfold avoids_zero, half. simpl. exact I. Qed.

Theorem third_avoids_zero : avoids_zero third.
Proof. unfold avoids_zero, third. simpl. exact I. Qed.

End Void_Probability_Minimal.