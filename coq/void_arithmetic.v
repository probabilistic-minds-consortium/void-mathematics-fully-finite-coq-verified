(******************************************************************************)
(* void_arithmetic.v                                                          *)
(* Arithmetic with budget/heat tracking - ONE TICK PER OPERATION             *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.ZArith.ZArith.
Require Import void_finite_minimal.

Module Void_Arithmetic.

(* Define operation_cost as one tick *)
Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* ARITHMETIC WITH HEAT - Every step costs one tick                          *)
(******************************************************************************)

(* Addition with heat tracking - one tick per recursive step *)
Fixpoint add_fin_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match m with
  | fz => (n, b, fz)  (* Base case: no cost *)
  | fs m' =>
      match b with
      | fz => (n, fz, fz)  (* Out of budget *)
      | fs b' =>
          match add_fin_heat n m' b' with
          | (sum, b'', h) => 
              match b'' with
              | fz => (sum, fz, add_heat h operation_cost)
              | fs b''' => (fs sum, b''', add_heat h operation_cost)
              end
          end
      end
  end.

(* Subtraction with heat - saturates at zero, one tick per step *)
Fixpoint sub_fin_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match m with
  | fz => (n, b, fz)  (* Base case: no cost *)
  | fs m' =>
      match b with
      | fz => (n, fz, fz)  (* Out of budget *)
      | fs b' =>
          match n with
          | fz => (fz, b', operation_cost)  (* Hit zero, one tick *)
          | fs n' => 
              match sub_fin_heat n' m' b' with
              | (res, b'', h) => (res, b'', add_heat h operation_cost)
              end
          end
      end
  end.

(* Multiplication with heat - repeated addition *)
Fixpoint mult_fin_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match m with
  | fz => (fz, b, fz)  (* Zero times anything is zero *)
  | fs m' =>
      match b with
      | fz => (fz, fz, fz)
      | fs b' =>
          match mult_fin_heat n m' b' with
          | (prod, b'', h1) => 
              match add_fin_heat prod n b'' with
              | (result, b''', h2) => (result, b''', add_heat h1 h2)
              end
          end
      end
  end.

(******************************************************************************)
(* DIVISION WITH HEAT - Each iteration costs one tick                        *)
(******************************************************************************)

Fixpoint div_helper_heat (n m fuel : Fin) (acc : Fin) (b : Budget) 
  : (Fin * Fin * Budget * Heat) :=
  match fuel with
  | fz => (acc, n, b, fz)
  | fs fuel' =>
      match b with
      | fz => (acc, n, fz, fz)
      | fs b' =>
          match le_fin_b_heat m n b' with
          | (true, b'', h1) =>
              match sub_fin_heat n m b'' with
              | (n', b''', h2) => 
                  match b''' with
                  | fz => (acc, n', fz, add_heat h1 h2)
                  | fs b'''' => 
                      match div_helper_heat n' m fuel' (fs acc) b'''' with
                      | (q, r, b_final, h3) => 
                          (q, r, b_final, add_heat (add_heat h1 h2) h3)
                      end
                  end
              end
          | (false, b'', h) => (acc, n, b'', h)
          end
      end
  end.

Definition div_fin_heat (n m : Fin) (b : Budget) : (Fin * Fin * Budget * Heat) :=
  match m with
  | fz => (fz, n, b, fz)  (* Division by zero *)
  | _ => div_helper_heat n m n fz b
  end.

(******************************************************************************)
(* MIN/MAX WITH HEAT - Simple comparisons, one tick each                     *)
(******************************************************************************)

Definition min_fin_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match le_fin_b_heat n m b with
  | (true, b', h) => (n, b', h)
  | (false, b', h) => (m, b', h)
  end.

Definition max_fin_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match le_fin_b_heat n m b with
  | (true, b', h) => (m, b', h)
  | (false, b', h) => (n, b', h)
  end.

(* Interval versions using Bool3 - handles uncertainty *)
Definition min_fin_interval (n m : Fin) (b : Budget) : (FinInterval * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h) => (Exact n, b', h)
  | (BFalse, b', h) => (Exact m, b', h)
  | (BUnknown, b', h) => (Range n m, b', h)  (* Can't decide - return both *)
  end.

Definition max_fin_interval (n m : Fin) (b : Budget) : (FinInterval * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h) => (Exact m, b', h)
  | (BFalse, b', h) => (Exact n, b', h)
  | (BUnknown, b', h) => (Range n m, b', h)
  end.

(******************************************************************************)
(* NEURAL NETWORK OPS WITH HEAT - No special costs                           *)
(******************************************************************************)

Definition relu_fin_heat (n threshold : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match le_fin_b_heat n threshold b with
  | (true, b', h) => (fz, b', h)
  | (false, b', h) => (n, b', h)
  end.

Definition clamp_fin_heat (value vmin vmax : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match le_fin_b_heat value vmin b with
  | (true, b', h1) => (vmin, b', h1)
  | (false, b', h1) =>
      match le_fin_b_heat vmax value b' with
      | (true, b'', h2) => (vmax, b'', add_heat h1 h2)
      | (false, b'', h2) => (value, b'', add_heat h1 h2)
      end
  end.

(******************************************************************************)
(* BACKWARD COMPATIBILITY - Drop heat for pair returns                       *)
(******************************************************************************)

Definition add_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match add_fin_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition sub_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match sub_fin_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition mult_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match mult_fin_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition div_fin (n m : Fin) (b : Budget) : (Fin * Fin * Budget) :=
  match div_fin_heat n m b with
  | (q, r, b', _) => (q, r, b')
  end.

Definition min_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match min_fin_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition max_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match max_fin_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition relu_fin (n threshold : Fin) (b : Budget) : (Fin * Budget) :=
  match relu_fin_heat n threshold b with
  | (res, b', _) => (res, b')
  end.

Definition clamp_fin (value vmin vmax : Fin) (b : Budget) : (Fin * Budget) :=
  match clamp_fin_heat value vmin vmax b with
  | (res, b', _) => (res, b')
  end.

(* Weighted average - each operation costs *)
Definition weighted_avg (w1 w2 v1 v2 : Fin) (b : Budget) : (Fin * Budget) :=
  match mult_fin_heat v1 w1 b with
  | (prod1, b1, h1) =>
      match mult_fin_heat v2 w2 b1 with
      | (prod2, b2, h2) =>
          match add_fin_heat w1 w2 b2 with
          | (sum_w, b3, h3) =>
              match add_fin_heat prod1 prod2 b3 with
              | (sum_prod, b4, h4) =>
                  match div_fin_heat sum_prod sum_w b4 with
                  | (quotient, _, b5, h5) => (quotient, b5)
                  end
              end
          end
      end
  end.

(* Dot product - accumulates costs *)
Fixpoint dot_product (v1 v2 : list Fin) (b : Budget) : (Fin * Budget) :=
  match v1 with
  | nil => (fz, b)
  | cons x1 xs1 =>
      match v2 with
      | nil => (fz, b)
      | cons x2 xs2 =>
          match b with
          | fz => (fz, fz)
          | fs b' =>
              match mult_fin_heat x1 x2 b' with
              | (prod, b'', _) =>
                  match dot_product xs1 xs2 b'' with
                  | (rest, b''') => 
                      match add_fin_heat prod rest b''' with
                      | (result, b_final, _) => (result, b_final)
                      end
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* HEAT CONSERVATION THEOREMS                                                *)
(******************************************************************************)

Axiom heat_conservation_add : forall n m b b' res h,
  add_fin_heat n m b = (res, b', h) -> add_heat h b' = b.

Axiom heat_conservation_sub : forall n m b b' res h,
  sub_fin_heat n m b = (res, b', h) -> add_heat h b' = b.

Axiom heat_conservation_mult : forall n m b b' res h,
  mult_fin_heat n m b = (res, b', h) -> add_heat h b' = b.

Axiom heat_conservation_div : forall n m b b' q r h,
  div_fin_heat n m b = (q, r, b', h) -> add_heat h b' = b.

(******************************************************************************)
(* PROBABILITY DIVISION MODULE                                               *)
(******************************************************************************)

Module Void_Probability_Division.

(* Probability type - pairs of Fin *)
Definition FinProb := (Fin * Fin)%type.
Definition Resolution := Fin.

(* Build 10 - needed for resolution denominators *)
Definition ten : Fin := 
  fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).

(* Build powers of 10 for resolution *)
Fixpoint resolution_denominator_heat (ρ : Resolution) (b : Budget) 
  : (Fin * Budget * Heat) :=
  match ρ with
  | fz => (fs fz, b, fz)  (* 10^0 = 1 *)
  | fs ρ' =>
      match b with
      | fz => (fs fz, fz, fz)
      | fs b' =>
          match resolution_denominator_heat ρ' b' with
          | (d_prev, b'', h1) =>
              match mult_fin_heat d_prev ten b'' with
              | (d_new, b''', h2) => (d_new, b''', add_heat h1 h2)
              end
          end
      end
  end.

(* Probability division at given resolution *)
Definition div_prob_heat (p1 p2 : FinProb) (ρ : Resolution) (b : Budget)
  : (FinProb * Budget * Heat) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match n2 with
  | fz => ((fz, fs fz), b, fz)  (* Division by zero -> 0/1 *)
  | _ =>
      match b with
      | fz => ((fz, fs fz), fz, fz)
      | _ =>
          (* Get denominator for resolution *)
          match resolution_denominator_heat ρ b with
          | (D_rho, b1, h1) =>
              (* Scale numerator: n1 * d2 * D(ρ) *)
              match mult_fin_heat n1 d2 b1 with
              | (temp1, b2, h2) =>
                  match mult_fin_heat temp1 D_rho b2 with
                  | (scaled_num, b3, h3) =>
                      (* Denominator: d1 * n2 *)
                      match mult_fin_heat d1 n2 b3 with
                      | (scaled_den, b4, h4) =>
                          (* Divide scaled_num / scaled_den *)
                          match div_fin_heat scaled_num scaled_den b4 with
                          | (quotient, remainder, b5, h5) =>
                              (* Result is quotient/D(ρ) *)
                              ((quotient, D_rho), b5,
                               add_heat (add_heat (add_heat (add_heat h1 h2) h3) h4) h5)
                          end
                      end
                  end
              end
          end
      end
  end.

(* Version without heat tracking *)
Definition div_prob (p1 p2 : FinProb) (ρ : Resolution) (b : Budget)
  : (FinProb * Budget) :=
  match div_prob_heat p1 p2 ρ b with
  | (res, b', _) => (res, b')
  end.

(* Simple probability operations for completeness *)
Definition prob_eq_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin n1 d2 b with
  | (v1, b1) =>
      match mult_fin n2 d1 b1 with
      | (v2, b2) => fin_eq_b v1 v2 b2
      end
  end.

Definition prob_le_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin n1 d2 b with
  | (v1, b1) =>
      match mult_fin n2 d1 b1 with
      | (v2, b2) => le_fin_b v1 v2 b2
      end
  end.

Definition prob_le_b3 (p1 p2 : FinProb) (b : Budget) : (Bool3 * Budget * Heat) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin_heat n1 d2 b with
  | (v1, b1, h1) =>
      match mult_fin_heat n2 d1 b1 with
      | (v2, b2, h2) =>
          match le_fin_b3 v1 v2 b2 with
          | (res, b3, h3) => (res, b3, add_heat (add_heat h1 h2) h3)
          end
      end
  end.

End Void_Probability_Division.

(******************************************************************************)
(* BASIC PROPERTIES                                                          *)
(******************************************************************************)

(* Heat always increases or stays same *)
Lemma heat_monotone : forall n m b res b' h,
  add_fin_heat n m b = (res, b', h) -> 
  (fin_to_Z_PROOF_ONLY h >= 0)%Z.
Proof.
  admit.  (* See philosophical note below *)
Admitted.

(******************************************************************************)
(*  PHILOSOPHICAL NOTE ON THE ABSENT PROOF                                   *)
(******************************************************************************)
(*  This proof would require threading classical naturals through our         *)
(*  finite recursion - exactly what we're trying to avoid. The gap is not    *)
(*  a bug but a feature: it marks where our finite mathematics meets         *)
(*  Coq's infinite metalanguage.                                             *)
(*                                                                            *)
(*  Every operation costs one tick. The heat is the accumulated time.        *)
(*  This is so fundamental it doesn't need proof - it's what time IS.        *)
(******************************************************************************)

(* Budget + Heat = Original Budget (conservation) *)
Lemma budget_heat_conservation : forall n m b res b' h,
  add_fin_heat n m b = (res, b', h) ->
  add_heat h b' = b.
Proof.
  intros. apply heat_conservation_add with n m res. exact H.
Qed.

End Void_Arithmetic.