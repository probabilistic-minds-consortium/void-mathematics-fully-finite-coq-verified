Require Import void_finite_minimal.
Require Import void_probability_minimal.
Import Void_Probability_Minimal.
Require Import List.
Import ListNotations.

(******************************************************************************)
(* PATTERN WITH DISTINGUISHABILITY                                           *)
(******************************************************************************)

Record DistPattern := {
  pattern_id : nat;
  distinguishability : FinProb
}.

(* Threshold for "actually distinguishable" - 2/5 *)
Definition threshold : FinProb := (fs (fs fz), fs (fs (fs (fs (fs fz))))).

(* Check if pattern exceeds threshold using existing prob_le_b3 *)
Definition above_threshold (p : DistPattern) (b : Budget) : (Bool3 * Budget * Heat) :=
  prob_le_b3 threshold (distinguishability p) b.

(* Count patterns above threshold *)
Fixpoint count_distinguishable (patterns : list DistPattern) (b : Budget) 
  : (nat * Budget * Heat) :=
  match patterns with
  | [] => (O, b, fz)
  | p :: ps =>
      match above_threshold p b with
      | (BTrue, b', h1) =>
          match count_distinguishable ps b' with
          | (n, b'', h2) => (S n, b'', add_heat h1 h2)
          end
      | (BFalse, b', h1) =>
          match count_distinguishable ps b' with
          | (n, b'', h2) => (n, b'', add_heat h1 h2)
          end
      | (BUnknown, b', h) =>
          (* Can't determine - stop counting *)
          (O, b', h)
      end
  end.

(* The emergent natural number *)
Definition emergent_natural (patterns : list DistPattern) (b : Budget) : nat :=
  match count_distinguishable patterns b with
  | (n, _, _) => n
  end.

(******************************************************************************)
(* CONCRETE EXAMPLE                                                          *)
(******************************************************************************)

(* Helper to make FinProb fractions *)
Definition make_prob (n d : nat) : FinProb :=
  (fst (mk_fin_b n initial_budget), fst (mk_fin_b d initial_budget)).

(* 5 patterns with different distinguishabilities *)
Definition p1 := {| pattern_id := 1; distinguishability := make_prob 3 5 |}.
Definition p2 := {| pattern_id := 2; distinguishability := make_prob 1 5 |}.
Definition p3 := {| pattern_id := 3; distinguishability := make_prob 4 5 |}.
Definition p4 := {| pattern_id := 4; distinguishability := make_prob 2 5 |}.
Definition p5 := {| pattern_id := 5; distinguishability := make_prob 4 5 |}.

Definition test_patterns := [p1; p2; p3; p4; p5].

(* Helper to build big Fin values *)
Fixpoint repeat_fs (n : nat) (base : Fin) : Fin :=
  match n with
  | O => base
  | S n' => fs (repeat_fs n' base)
  end.

(* Budget that's 100 more than initial *)
Definition huge_budget : Budget := repeat_fs 100 initial_budget.

(* Or just make budget of size 100 from scratch *)
Definition budget_100 : Budget := repeat_fs 100 fz.

(* Test with huge budget *)
Compute (emergent_natural test_patterns huge_budget).

Example test_emergence :
  emergent_natural test_patterns huge_budget = 3%nat.
Proof.
  reflexivity.
Qed.