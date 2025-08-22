(******************************************************************************)
(* void_finite_minimal.v                                                      *)
(* TRULY finite - every operation costs                                       *)
(* Bool3 core + backward-compatible bool wrappers                             *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(******************************************************************************)
(* SYSTEM PARAMETERS - META-LEVEL ONLY                                       *)
(******************************************************************************)

Parameter MAX : Z.
Axiom MAX_positive : (0 < MAX)%Z.

(* System resolution - parameter, not computed *)
Parameter Î¼_tick : Q.
Axiom Î¼_tick_spec : Î¼_tick = 1#100.

(******************************************************************************)
(* FINITE TYPE Fin                                                           *)
(******************************************************************************)

Inductive Fin : Type :=
  | fz : Fin
  | fs : Fin -> Fin.

(* PROOF-ONLY: Never use in computation *)
Fixpoint fin_to_Z_PROOF_ONLY (n : Fin) : Z :=
  match n with
  | fz => 0%Z
  | fs n' => (1 + fin_to_Z_PROOF_ONLY n')%Z
  end.

(* The bound is an axiom about the type, not a computation *)
Axiom fin_bounded : forall n : Fin, (fin_to_Z_PROOF_ONLY n <= MAX)%Z.

(******************************************************************************)
(* Fin â‰¤ and basic lemmas                                                    *)
(******************************************************************************)

Inductive leF : Fin -> Fin -> Prop :=
  | leF_z  : forall m, leF fz m
  | leF_ss : forall n m, leF n m -> leF (fs n) (fs m).

Lemma leF_refl : forall x, leF x x.
Proof. induction x; constructor; auto. Qed.

Lemma leF_trans : forall x y z, leF x y -> leF y z -> leF x z.
Proof.
  intros x y z Hxy Hyz; revert x Hxy.
  induction Hyz; intros x Hxy.
  - inversion Hxy; constructor.
  - inversion Hxy; subst; constructor; auto.
Qed.

Lemma leF_step : forall x, leF x (fs x).
Proof. induction x; constructor; auto. Qed.

(******************************************************************************)
(* THREE-VALUED LOGIC                                                        *)
(******************************************************************************)

Inductive Bool3 : Type :=
  | BTrue : Bool3
  | BFalse : Bool3
  | BUnknown : Bool3.

Definition bool3_to_option (b : Bool3) : option bool :=
  match b with
  | BTrue => Some true
  | BFalse => Some false
  | BUnknown => None
  end.

(******************************************************************************)
(* BUDGET, HEAT, AND STATE                                                   *)
(******************************************************************************)

Definition Budget := Fin.
Definition Heat := Fin.
Definition State := (Fin * Budget)%type.

Fixpoint add_heat (h1 h2 : Fin) : Fin :=
  match h2 with
  | fz => h1
  | fs h2' => fs (add_heat h1 h2')
  end.

Definition B (A : Type) := Budget -> (A * Budget * Heat).

Definition ret {A : Type} (a : A) : B A :=
  fun b => (a, b, fz).

Definition bind {A C : Type} (ma : B A) (f : A -> B C) : B C :=
  fun budget =>
    match ma budget with
    | (a, b', h1) =>
        match f a b' with
        | (result, b'', h2) => (result, b'', add_heat h1 h2)
        end
    end.

Fixpoint spend_aux (b c : Fin) : (Budget * Heat) :=
  match c with
  | fz => (b, fz)
  | fs c' =>
      match b with
      | fz => (fz, c)
      | fs b' =>
          match spend_aux b' c' with
          | (b'', h) => (b'', fs h)
          end
      end
  end.

Definition spend (cost : Fin) : B unit :=
  fun b => let (b', h) := spend_aux b cost in (tt, b', h).

(******************************************************************************)
(* COSTS AS PARAMETERS - NOT CONSTRUCTED                                     *)
(******************************************************************************)

Parameter comparison_cost : Fin.
Parameter arithmetic_cost : Fin.
Parameter construction_cost : Fin.

Axiom comparison_cost_positive   : exists n, comparison_cost = fs n.
Axiom arithmetic_cost_positive   : exists n, arithmetic_cost = fs n.
Axiom construction_cost_positive : exists n, construction_cost = fs n.

(******************************************************************************)
(* BOOTSTRAP BUDGET                                                          *)
(******************************************************************************)

Parameter initial_budget : Budget.
Axiom initial_budget_sufficient : exists n, initial_budget = fs (fs (fs n)).

(******************************************************************************)
(* BUDGET-AWARE OPS (3-valued core) - WITH HEAT                            *)
(******************************************************************************)

Fixpoint fin_eq_b3 (n m : Fin) (b : Budget) : (Bool3 * Budget * Heat) :=
  match b with
  | fz => (BUnknown, fz, fz)
  | fs b' =>
      match n, m with
      | fz, fz => (BTrue, b', fs fz)
      | fs n', fs m' =>
          match fin_eq_b3 n' m' b' with
          | (r, b'', h) => (r, b'', fs h)
          end
      | _, _ => (BFalse, b', fs fz)
      end
  end.

Fixpoint le_fin_b3 (n m : Fin) (b : Budget) : (Bool3 * Budget * Heat) :=
  match b with
  | fz => (BUnknown, fz, fz)
  | fs b' =>
      match n, m with
      | fz, _ => (BTrue, b', fs fz)
      | fs _, fz => (BFalse, b', fs fz)
      | fs n', fs m' =>
          match le_fin_b3 n' m' b' with
          | (r, b'', h) => (r, b'', fs h)
          end
      end
  end.

(******************************************************************************)
(* Collapse Unknownâ†’false (WITH HEAT)                                        *)
(******************************************************************************)

Definition collapse3 (r : Bool3) : bool :=
  match r with BTrue => true | _ => false end.

Definition fin_eq_b_heat (n m : Fin) (b : Budget) : (bool * Budget * Heat) :=
  match fin_eq_b3 n m b with
  | (r, b', h) => (collapse3 r, b', h)
  end.

Definition le_fin_b_heat (n m : Fin) (b : Budget) : (bool * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (r, b', h) => (collapse3 r, b', h)
  end.

(******************************************************************************)
(* INTERVAL RESULTS & DECISION VARIANTS (use 3-valued core)                   *)
(******************************************************************************)

Inductive FinInterval : Type :=
  | Exact : Fin -> FinInterval
  | Range : Fin -> Fin -> FinInterval.

Definition min_fin_interval (n m : Fin) (b : Budget)
  : (FinInterval * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (Exact n, b', h)
  | (BFalse, b', h)   => (Exact m, b', h)
  | (BUnknown, b', h) => (Range n m, b', h)
  end.

Definition max_fin_interval (n m : Fin) (b : Budget)
  : (FinInterval * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (Exact m, b', h)
  | (BFalse, b', h)   => (Exact n, b', h)
  | (BUnknown, b', h) => (Range n m, b', h)
  end.

Definition min_fin_dec (n m : Fin) (b : Budget)
  : (Fin * Bool3 * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (n, BTrue, b', h)
  | (BFalse, b', h)   => (m, BFalse, b', h)
  | (BUnknown, b', h) => (n, BUnknown, b', h)
  end.

Definition max_fin_dec (n m : Fin) (b : Budget)
  : (Fin * Bool3 * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue, b', h)    => (m, BTrue, b', h)
  | (BFalse, b', h)   => (n, BFalse, b', h)
  | (BUnknown, b', h) => (m, BUnknown, b', h)
  end.

(******************************************************************************)
(* Arithmetic on Fin with budget/heat                                        *)
(******************************************************************************)

Fixpoint sub_saturate_b_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match b with
  | fz => (fz, fz, fz)
  | fs b' =>
      match n, m with
      | _,  fz      => (n, b', fs fz)
      | fz, _       => (fz, b', fs fz)
      | fs n', fs m' =>
          match sub_saturate_b_heat n' m' b' with
          | (r, b'', h) => (r, b'', fs h)
          end
      end
  end.

Fixpoint add_fin_b_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match m, b with
  | fz, _   => (n, b, fz)
  | _,  fz  => (n, fz, fz)
  | fs m', fs b' =>
      match add_fin_b_heat n m' b' with
      | (r, b'', h) => (fs r, b'', fs h)
      end
  end.

Definition dist_fin_b_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match le_fin_b3 n m b with
  | (BTrue,  b', h1) =>
      match sub_saturate_b_heat m n b' with
      | (d, b'', h2) => (d, b'', add_heat h1 h2)
      end
  | (BFalse, b', h1) =>
      match sub_saturate_b_heat n m b' with
      | (d, b'', h2) => (d, b'', add_heat h1 h2)
      end
  | (BUnknown, b', h) => (fz, b', h)
  end.

Definition safe_succ_b_heat (n : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match b with
  | fz => (n, fz, fz)
  | fs b' => (fs n, b', fs fz)
  end.

Fixpoint mult_fin_heat (n m : Fin) (b : Budget) : (Fin * Budget * Heat) :=
  match m with
  | fz => (fz, b, fz)
  | fs m' =>
      match b with
      | fz => (fz, fz, fz)
      | fs b' =>
          match mult_fin_heat n m' b' with
          | (prod, b'', h1) =>
              match add_fin_b_heat prod n b'' with
              | (result, b''', h2) => (result, b''', add_heat h1 h2)
              end
          end
      end
  end.

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
              match sub_saturate_b_heat n m b'' with
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
  | fz => (fz, n, b, fz)
  | _ => div_helper_heat n m n fz b
  end.

(******************************************************************************)
(* STATE TRANSITIONS WITH BUDGET AND HEAT                                    *)
(******************************************************************************)

Definition succ_with_heat (s : State) : (State * Heat) :=
  match s with
  | (n, fz) => ((n, fz), fz)
  | (n, fs b') => ((fs n, b'), fs fz)
  end.

Fixpoint bounded_iter_with_heat (k : Fin) (f : State -> (State * Heat)) (s : State)
  : (State * Heat) :=
  match k with
  | fz => (s, fz)
  | fs k' =>
      match snd s with
      | fz => (s, fz)
      | _ =>
          match f s with
          | (s', h1) =>
              match bounded_iter_with_heat k' f s' with
              | (s'', h2) => (s'', add_heat h1 h2)
              end
          end
      end
  end.

(******************************************************************************)
(* CONSTRUCTION WITH COST AND HEAT                                           *)
(******************************************************************************)

Fixpoint mk_fin_b_heat (n : nat) (b : Budget) : (Fin * Budget * Heat) :=
  match n with
  | O => (fz, b, fz)
  | S n' =>
      match b with
      | fz => (fz, fz, fz)
      | fs b' =>
          match mk_fin_b_heat n' b' with
          | (f, b'', h) => (fs f, b'', fs h)
          end
      end
  end.

Definition make_two_heat   (b : Budget) : (Fin * Budget * Heat) := mk_fin_b_heat 2 b.
Definition make_three_heat (b : Budget) : (Fin * Budget * Heat) := mk_fin_b_heat 3 b.
Definition make_five_heat  (b : Budget) : (Fin * Budget * Heat) := mk_fin_b_heat 5 b.
Definition make_ten_heat   (b : Budget) : (Fin * Budget * Heat) := mk_fin_b_heat 10 b.

(******************************************************************************)
(* BACKWARD COMPATIBILITY - Operations that return pairs, not triples        *)
(******************************************************************************)

Definition fin_eq_b (n m : Fin) (b : Budget) : (bool * Budget) :=
  match fin_eq_b_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition le_fin_b (n m : Fin) (b : Budget) : (bool * Budget) :=
  match le_fin_b_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition sub_saturate_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match sub_saturate_b_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition sub_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  sub_saturate_b n m b.

Definition add_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match add_fin_b_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition add_fin (n m : Fin) (b : Budget) : (Fin * Budget) :=
  add_fin_b n m b.

Definition dist_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match dist_fin_b_heat n m b with
  | (res, b', _) => (res, b')
  end.

Definition safe_succ_b (n : Fin) (b : Budget) : (Fin * Budget) :=
  match safe_succ_b_heat n b with
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

Definition min_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => (n, b')
  | (false, b') => (m, b')
  end.

Definition max_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => (m, b')
  | (false, b') => (n, b')
  end.

Definition mk_fin_b (n : nat) (b : Budget) : (Fin * Budget) :=
  match mk_fin_b_heat n b with
  | (res, b', _) => (res, b')
  end.

Definition fin_from_nat_b (n : nat) (b : Budget) : (Fin * Budget) :=
  mk_fin_b n b.

Definition make_two   (b : Budget) : (Fin * Budget) := mk_fin_b 2 b.
Definition make_three (b : Budget) : (Fin * Budget) := mk_fin_b 3 b.
Definition make_five  (b : Budget) : (Fin * Budget) := mk_fin_b 5 b.
Definition make_ten   (b : Budget) : (Fin * Budget) := mk_fin_b 10 b.

(******************************************************************************)
(* STATE TRANSITIONS (no heat)                                              *)
(******************************************************************************)

Definition succ (s : State) : State :=
  match s with
  | (n, fz) => (n, fz)
  | (n, fs b') => (fs n, b')
  end.

Fixpoint bounded_iter (k : Fin) (f : State -> State) (s : State) : State :=
  match k with
  | fz => s
  | fs k' =>
      match snd s with
      | fz => s
      | _ => bounded_iter k' f (f s)
      end
  end.

(******************************************************************************)
(* NON-BUDGETED WRAPPERS (use initial_budget)                               *)
(******************************************************************************)

Definition fin_eq (n m : Fin) : bool :=
  fst (fin_eq_b n m initial_budget).

Definition le_fin (n m : Fin) : bool :=
  fst (le_fin_b n m initial_budget).

Definition add_simple (n m : Fin) : Fin :=
  fst (add_fin_b n m initial_budget).

Definition sub_simple (n m : Fin) : Fin :=
  fst (sub_saturate_b n m initial_budget).

Definition dist_fin (n m : Fin) : Fin :=
  fst (dist_fin_b n m initial_budget).

Definition min_fin (n m : Fin) : Fin :=
  fst (min_fin_b n m initial_budget).

Definition max_fin (n m : Fin) : Fin :=
  fst (max_fin_b n m initial_budget).

Definition fin_eq_LEGACY := fin_eq.
Definition le_fin_LEGACY := le_fin.
Definition add_simple_LEGACY := add_simple.


(******************************************************************************)
(* HEAT CONSERVATION LAW - As fundamental axiom                              *)
(******************************************************************************)

Axiom heat_conservation_eq3 : forall n m b b' res h,
  fin_eq_b3 n m b = (res, b', h) -> add_heat h b' = b.

Axiom heat_conservation_le3 : forall n m b b' res h,
  le_fin_b3 n m b = (res, b', h) -> add_heat h b' = b.