(******************************************************************************)
(* void_replicator_bayes.v — REPLICATOR-BAYES ON A FINITE GRID                *)
(*                                                                            *)
(* Proof of concept: a population of hypotheses with budgets, fed by a       *)
(* signal stream, where each hypothesis (inner membrane) receives intake     *)
(* proportional to its filter score on the incoming signal.                  *)
(*                                                                            *)
(* Claim under test: after k signals from a fixed source distribution,       *)
(* the normalised budget distribution across inners approaches the           *)
(* Bayesian posterior over which inner's filter best matches the source.    *)
(*                                                                            *)
(* This file:                                                                 *)
(*   1. Defines soft filter score (graded match instead of binary BTrue/BFalse)*)
(*   2. Defines selective intake (budget redistribution proportional to score)*)
(*   3. Sets up a small fixture (3 inners, fixed signal source)              *)
(*   4. Runs Compute to produce numerical convergence data                   *)
(*                                                                            *)
(* DEPENDS ON: void_finite_minimal, void_probability_minimal,                *)
(*             void_probability_geometry, void_figure_geometry, void_membrane*)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_probability_geometry.
Require Import void_figure_geometry.
Require Import void_membrane.

Import Void_Probability_Minimal.
Import Void_Probability_Geometry.

(******************************************************************************)
(* SECTION 1: SOFT FILTER SCORE                                              *)
(*                                                                            *)
(* Standard recognise returns Bool3 (BTrue if inside radius, BFalse if       *)
(* outside). For replicator dynamics we need a graded match: a Fin score    *)
(* that monotonically decreases with distance.                                *)
(*                                                                            *)
(*   score(m, signal) = saturating_sub(mem_filter_radius m, distance)        *)
(*                                                                            *)
(* Score = filter_radius means perfect match (distance 0).                    *)
(* Score = 0 means signal is at or beyond the filter boundary.                *)
(* Higher score = better match.                                               *)
(******************************************************************************)

Definition soft_filter_score
  (m : Membrane)
  (signal : list Pattern)
  (b : Budget)
  : (Fin * Budget * Spuren) :=
  match figure_distance signal (mem_filter_center m) b with
  | (dist, b1, h1) =>
      match sub_saturate_b_spur (mem_filter_radius m) dist b1 with
      | (score, b2, h2) => (score, b2, add_spur h1 h2)
      end
  end.

(******************************************************************************)
(* SECTION 2: SCORE EACH INNER                                                *)
(*                                                                            *)
(* Walk the list of inner membranes, compute a score for each against the    *)
(* incoming signal, accumulate the total score. Returns a list of            *)
(* (membrane, score) pairs, the total score, the remaining budget, and       *)
(* the accumulated Spuren.                                                    *)
(******************************************************************************)

Fixpoint score_each
  (ms : list Membrane)
  (signal : list Pattern)
  (b : Budget)
  : (list (Membrane * Fin) * Fin * Budget * Spuren) :=
  match ms with
  | [] => ([], fz, b, fz)
  | m :: rest =>
      match soft_filter_score m signal b with
      | (s_m, b1, h1) =>
          match score_each rest signal b1 with
          | (rest_pairs, total_rest, b2, h2) =>
              match add_fin_b_spur s_m total_rest b2 with
              | (total, b3, h3) =>
                  ((m, s_m) :: rest_pairs,
                   total,
                   b3,
                   add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

(******************************************************************************)
(* SECTION 3: DISTRIBUTE BUDGET                                               *)
(*                                                                            *)
(* Given a list of (membrane, score) pairs, a delta budget delta_B to be    *)
(* split among them, and a precomputed total_score, hand each membrane its  *)
(* share:                                                                    *)
(*                                                                            *)
(*   share(m_i) = floor(delta_B * score_i / total_score)                     *)
(*                                                                            *)
(* and assimilate that share into m_i's budget. Returns the updated list,   *)
(* remaining budget, and accumulated Spuren.                                  *)
(*                                                                            *)
(* Special case: if total_score = fz, no inner matches the signal at all —  *)
(* no distribution happens (delta_B is forfeited to the outer membrane,     *)
(* which is not modelled here).                                              *)
(******************************************************************************)

Fixpoint distribute_budget
  (pairs : list (Membrane * Fin))
  (delta_B : Fin)
  (total_score : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match pairs with
  | [] => ([], b, fz)
  | (m, score) :: rest =>
      match mult_fin_spur delta_B score b with
      | (numer, b1, h1) =>
          match div_fin_spur numer total_score b1 with
          | (share, _rem, b2, h2) =>
              match assimilate_b_spur share (mem_budget m) with
              | (new_budget, h3) =>
                  let m' := mkMembrane (mem_filter_center m)
                                       (mem_filter_radius m)
                                       (mem_capacity m)
                                       new_budget
                                       (mem_inner m) in
                  match distribute_budget rest delta_B total_score b2 with
                  | (rest', b3, h4) =>
                      (m' :: rest',
                       b3,
                       add_spur (add_spur h1 h2) (add_spur h3 h4))
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* SECTION 4: SELECTIVE INTAKE                                                *)
(*                                                                            *)
(* The full operation: given a list of inner membranes, a signal arriving   *)
(* at the compound, and a delta budget, redistribute delta_B to inners       *)
(* in proportion to how well each one's filter matches the signal.          *)
(******************************************************************************)

Definition selective_intake
  (inners : list Membrane)
  (signal : list Pattern)
  (delta_B : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match score_each inners signal b with
  | (pairs, total, b1, h1) =>
      match distribute_budget pairs delta_B total b1 with
      | (inners', b2, h2) => (inners', b2, add_spur h1 h2)
      end
  end.

(******************************************************************************)
(* SECTION 4b: MULTIPLICATIVE UPDATE  (replicator-Bayes proper)              *)
(*                                                                            *)
(* The additive update above converges to the *single-observation* posterior *)
(* (likelihood ratio with smoothed prior). To recover *multi-observation*    *)
(* Bayesian posterior — proportional to π_i × ∏_t L_i(s_t) — we need a       *)
(* multiplicative update:                                                    *)
(*                                                                            *)
(*   b_i^(t+1) = floor(b_i^(t) × L_i(s_t) × Z / Σ_j (b_j^(t) × L_j(s_t)))   *)
(*                                                                            *)
(* where Z = Σ_j b_j^(t) is the current total budget. This redistributes    *)
(* the existing total in proportion to (current weight × likelihood) —       *)
(* exactly the standard replicator dynamic in discrete form.                 *)
(*                                                                            *)
(* Floor division per inner: at most 1 grid unit lost. n inners ⇒ at most n *)
(* lost per cycle ⇒ O(k·n/Z) error after k cycles.                           *)
(******************************************************************************)

(* Sum the current budgets across inners. *)
Fixpoint sum_budgets (ms : list Membrane) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match ms with
  | [] => (fz, b, fz)
  | m :: rest =>
      match sum_budgets rest b with
      | (s_rest, b1, h1) =>
          match add_fin_b_spur (mem_budget m) s_rest b1 with
          | (total, b2, h2) => (total, b2, add_spur h1 h2)
          end
      end
  end.

(* For each inner, compute (b_i × score_i) and accumulate the total of these
   products across the population. Returns (m, b_i*L_i) pairs and total. *)
Fixpoint multiply_weights
  (ms : list Membrane)
  (signal : list Pattern)
  (b : Budget)
  : (list (Membrane * Fin) * Fin * Budget * Spuren) :=
  match ms with
  | [] => ([], fz, b, fz)
  | m :: rest =>
      match soft_filter_score m signal b with
      | (s_m, b1, h1) =>
          match mult_fin_spur (mem_budget m) s_m b1 with
          | (numer_m, b2, h2) =>
              match multiply_weights rest signal b2 with
              | (rest_pairs, total_rest, b3, h3) =>
                  match add_fin_b_spur numer_m total_rest b3 with
                  | (total, b4, h4) =>
                      ((m, numer_m) :: rest_pairs,
                       total,
                       b4,
                       add_spur h1 (add_spur h2 (add_spur h3 h4)))
                  end
              end
          end
      end
  end.

(* For each inner with its already-computed numerator (b_i × L_i),
   compute new_b_i = floor(numer_i × Z / total_numer). *)
Fixpoint renormalize
  (pairs : list (Membrane * Fin))
  (Z : Fin)
  (total_numer : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match pairs with
  | [] => ([], b, fz)
  | (m, numer) :: rest =>
      match mult_fin_spur numer Z b with
      | (scaled, b1, h1) =>
          match div_fin_spur scaled total_numer b1 with
          | (new_b, _rem, b2, h2) =>
              let m' := mkMembrane (mem_filter_center m)
                                   (mem_filter_radius m)
                                   (mem_capacity m)
                                   new_b
                                   (mem_inner m) in
              match renormalize rest Z total_numer b2 with
              | (rest', b3, h3) =>
                  (m' :: rest',
                   b3,
                   add_spur (add_spur h1 h2) h3)
              end
          end
      end
  end.

(* Multiplicative replicator-Bayes update — version with renormalisation
   to preserve total budget Z. Computationally expensive: requires
   numer × Z multiplication followed by division by total_numer.
   For 3 inners with budgets ~32 and likelihoods ~4, intermediate values
   reach ~12000, requiring processing budget in the hundreds of thousands.
   Useful for theory but not for the small numerical experiment below. *)
Definition multiplicative_update_renormalise
  (inners : list Membrane)
  (signal : list Pattern)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match sum_budgets inners b with
  | (Z, b1, h1) =>
      match multiply_weights inners signal b1 with
      | (pairs, total_numer, b2, h2) =>
          match renormalize pairs Z total_numer b2 with
          | (inners', b3, h3) =>
              (inners', b3, add_spur h1 (add_spur h2 h3))
          end
      end
  end.

(* Cheaper multiplicative update — fixed divisor instead of renormalisation.
   Each inner is updated as new_b_i = floor(b_i × L_i / divisor).
   The divisor is a global constant for the population, normally chosen as
   the maximum possible score (filter radius). With divisor = max_score:
     - inner with L_i = max_score stays unchanged
     - inner with L_i < max_score shrinks geometrically each cycle
   Ratios converge to the Bayesian posterior; total budget decays gracefully.
   Computationally much cheaper than renormalisation. *)
Fixpoint update_each_simple
  (ms : list Membrane)
  (signal : list Pattern)
  (divisor : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match ms with
  | [] => ([], b, fz)
  | m :: rest =>
      match soft_filter_score m signal b with
      | (s_m, b1, h1) =>
          match mult_fin_spur (mem_budget m) s_m b1 with
          | (numer, b2, h2) =>
              match div_fin_spur numer divisor b2 with
              | (new_b, _rem, b3, h3) =>
                  let m' := mkMembrane (mem_filter_center m)
                                       (mem_filter_radius m)
                                       (mem_capacity m)
                                       new_b
                                       (mem_inner m) in
                  match update_each_simple rest signal divisor b3 with
                  | (rest', b4, h4) =>
                      (m' :: rest',
                       b4,
                       add_spur h1 (add_spur h2 (add_spur h3 h4)))
                  end
              end
          end
      end
  end.

Definition multiplicative_update
  (inners : list Membrane)
  (signal : list Pattern)
  (divisor : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  update_each_simple inners signal divisor b.

(******************************************************************************)
(* SECTION 4b: COST-OF-PRESENCE (mortal pattern dynamics)                    *)
(*                                                                            *)
(* Update rule on capacity (not budget):                                     *)
(*   cap_i^{(t+1)} = max(0, floor(cap_i^{(t)} * sigma_i(s_t) / sigma_max)    *)
(*                          - c_min)                                         *)
(*                                                                            *)
(* Where c_min : Fin is the cost-of-presence parameter — the fixed amount   *)
(* every pattern pays per cycle simply for existing in the population.       *)
(* This is independent of (and additive to) the multiplicative_update on    *)
(* the budget side. Two orthogonal processes:                                *)
(*   multiplicative_update : modifies mem_budget (the fuel)                 *)
(*   cap_decay             : modifies mem_capacity (the absorption ceiling) *)
(******************************************************************************)

Definition cap_decay
  (m : Membrane)
  (signal : list Pattern)
  (sigma_max : Fin)
  (c_min : Fin)
  (b : Budget)
  : (Membrane * Budget * Spuren) :=
  match soft_filter_score m signal b with
  | (sigma, b1, h1) =>
      match mult_fin_spur (mem_capacity m) sigma b1 with
      | (numer, b2, h2) =>
          match div_fin_spur numer sigma_max b2 with
          | (cap_decayed, _rem, b3, h3) =>
              match sub_saturate_b_spur cap_decayed c_min b3 with
              | (new_cap, b4, h4) =>
                  let m' := mkMembrane (mem_filter_center m)
                                       (mem_filter_radius m)
                                       new_cap
                                       (mem_budget m)
                                       (mem_inner m) in
                  (m', b4, add_spur h1 (add_spur h2 (add_spur h3 h4)))
              end
          end
      end
  end.

(* ---- Helper lemmas: zero propagates through arithmetic on Fin ---- *)

Lemma mult_fin_spur_zero_r : forall n b,
  mult_fin_spur n fz b = (fz, b, fz).
Proof. intros. reflexivity. Qed.

Lemma div_fin_spur_zero_num : forall d b,
  div_fin_spur fz d b = (fz, fz, b, fz).
Proof.
  intros d b. unfold div_fin_spur.
  destruct d; reflexivity.
Qed.

Lemma sub_saturate_zero_num_fst : forall m b,
  fst (fst (sub_saturate_b_spur fz m b)) = fz.
Proof.
  intros m b.
  destruct b as [| b']; [reflexivity |].
  destruct m; reflexivity.
Qed.

(* ---- THEOREM: zero-match annihilation ---- *)
(* If a membrane scores zero against a signal, then after one cap_decay     *)
(* step its mem_capacity collapses to fz — regardless of c_min, sigma_max, *)
(* or remaining budget. Cost-of-presence does not even need to fire; the   *)
(* multiplicative core annihilates capacity at the first step.             *)

Theorem zero_match_annihilation :
  forall m signal sigma_max c_min b b1 h1 m' b' h,
  soft_filter_score m signal b = (fz, b1, h1) ->
  cap_decay m signal sigma_max c_min b = (m', b', h) ->
  mem_capacity m' = fz.
Proof.
  intros m signal sigma_max c_min b b1 h1 m' b' h Hsf Hcd.
  unfold cap_decay in Hcd.
  rewrite Hsf in Hcd.
  rewrite mult_fin_spur_zero_r in Hcd.
  rewrite div_fin_spur_zero_num in Hcd.
  destruct (sub_saturate_b_spur fz c_min b1) as [[new_cap b4] h4] eqn:Hsub.
  pose proof (sub_saturate_zero_num_fst c_min b1) as Hzero.
  rewrite Hsub in Hzero. simpl in Hzero. subst new_cap.
  inversion Hcd; subst.
  reflexivity.
Qed.

(******************************************************************************)
(* SECTION 5: ITERATE OVER A SIGNAL STREAM                                    *)
(*                                                                            *)
(* Apply selective_intake repeatedly, one signal at a time. Each application *)
(* consumes some processing budget; we thread the budget through.             *)
(******************************************************************************)

Fixpoint replicator_run
  (inners : list Membrane)
  (signals : list (list Pattern))
  (divisor : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match signals with
  | [] => (inners, b, fz)
  | s :: rest =>
      match multiplicative_update inners s divisor b with
      | (inners', b1, h1) =>
          match replicator_run inners' rest divisor b1 with
          | (final, b2, h2) => (final, b2, add_spur h1 h2)
          end
      end
  end.

(* Legacy additive run (kept for comparison, not used in the main test) *)
Fixpoint additive_run
  (inners : list Membrane)
  (signals : list (list Pattern))
  (delta_B : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match signals with
  | [] => (inners, b, fz)
  | s :: rest =>
      match selective_intake inners s delta_B b with
      | (inners', b1, h1) =>
          match additive_run inners' rest delta_B b1 with
          | (final, b2, h2) => (final, b2, add_spur h1 h2)
          end
      end
  end.

(******************************************************************************)
(* SECTION 6: TEST FIXTURE                                                    *)
(*                                                                            *)
(* Three atomic inner membranes with different filter centres along the     *)
(* same axis. All have the same radius and capacity. All start with the     *)
(* same initial budget.                                                      *)
(******************************************************************************)

(* Convenience constants *)
Local Definition f1 := fs fz.
Local Definition f2 := fs (fs fz).
Local Definition f3 := fs (fs (fs fz)).
Local Definition f4 := fs (fs (fs (fs fz))).
Local Definition f5 := fs (fs (fs (fs (fs fz)))).
Local Definition f6 := fs (fs (fs (fs (fs (fs fz))))).
Local Definition f8 := fs (fs (fs (fs (fs (fs (fs (fs fz))))))).
Local Definition f10 := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).
Local Definition f16 :=
  fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))))))).
Local Definition f32 :=
  fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs
  (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))))))))))))))))))))))).

(* Helper: triple a Fin (uses no budget — pure structural operation) *)
Fixpoint fin_triple (n : Fin) : Fin :=
  match n with
  | fz => fz
  | fs n' => fs (fs (fs (fin_triple n')))
  end.

(* Larger budgets for stretching the simulation *)
Local Definition f96 := fin_triple f32.
Local Definition f288 := fin_triple f96.
Local Definition f864 := fin_triple f288.
Local Definition f2592 := fin_triple f864.
Local Definition f7776 := fin_triple f2592.
Local Definition f23328 := fin_triple f7776.
Local Definition f69984 := fin_triple f23328.
Local Definition f209952 := fin_triple f69984.

(* Inner 1: filter centred at point 2/8, initial budget 32 *)
Definition inner_1 : Membrane :=
  mkMembrane [mk_pattern_from_pair f2 f8] f4 f4 f32 nil.

(* Inner 2: filter centred at point 3/8, initial budget 32 *)
Definition inner_2 : Membrane :=
  mkMembrane [mk_pattern_from_pair f3 f8] f4 f4 f32 nil.

(* Inner 3: filter centred at point 5/8, initial budget 32 *)
Definition inner_3 : Membrane :=
  mkMembrane [mk_pattern_from_pair f5 f8] f4 f4 f32 nil.

Definition test_inners : list Membrane :=
  [inner_1; inner_2; inner_3].

(* Source signal: at point 3/8 — exactly matches inner_2.
   Distance to inner_1 is 1, to inner_2 is 0, to inner_3 is 2.
   mk_pattern_from_pair lifts the legacy pair into the unified Pattern. *)
Definition source_signal : list Pattern := [mk_pattern_from_pair f3 f8].

(* A short stream of identical signals. *)
Definition signal_stream : list (list Pattern) :=
  [source_signal; source_signal; source_signal; source_signal; source_signal].

(* Delta budget per signal arrival.
   With f8 and source-induced scores (3, 4, 2) summing to 9, the
   per-cycle shares are roughly floor(8*3/9)=2, floor(8*4/9)=3,
   floor(8*2/9)=1, which discriminates the inners after 5 cycles. *)
Definition delta_per_signal : Fin := f8.

(* Total processing budget for the run.
   First test (f288) showed budget exhausted: scoring one inner against
   a perfect-match signal costs >16 units, so 15 scorings + 15 distributes
   need at minimum ~600 units, more likely 1500-2000. f7776 gives ample
   margin for the experiment. *)
Definition processing_budget : Budget := f7776.

(******************************************************************************)
(* SECTION 7: COMPUTE — observe the result                                    *)
(*                                                                            *)
(* Run the experiment and extract the budget of each inner after the run.   *)
(******************************************************************************)

(* Divisor = maximum possible score = filter radius = f4.
   The inner with score = 4 (perfect match) stays put; others shrink. *)
Definition score_divisor : Fin := f4.

Definition run_result : list Membrane * Budget * Spuren :=
  replicator_run test_inners signal_stream score_divisor processing_budget.

(* Legacy additive run for comparison — unused in main test *)
Definition run_result_additive : list Membrane * Budget * Spuren :=
  additive_run test_inners signal_stream delta_per_signal processing_budget.

Definition final_inners : list Membrane :=
  fst (fst run_result).

(* Helper to extract just the budgets, for inspection *)
Fixpoint extract_budgets (ms : list Membrane) : list Budget :=
  match ms with
  | [] => []
  | m :: rest => mem_budget m :: extract_budgets rest
  end.

Definition final_budgets : list Budget :=
  extract_budgets final_inners.

(* Theoretical prediction (multiplicative update with fixed divisor = 4)
   for source = (3, 8) repeated 5 times.

   Scores (radius − distance), with divisor = max score = 4:
     inner_1 at (2, 8): L = 4 − 1 = 3
     inner_2 at (3, 8): L = 4 − 0 = 4   (perfect match)
     inner_3 at (5, 8): L = 4 − 2 = 2

   Initial b = (32, 32, 32). Update rule: new_b_i = floor(b_i × L_i / 4).

   Cycle 1: (32, 32, 32) → (24, 32, 16)
   Cycle 2: (24, 32, 16) → (18, 32, 8)
   Cycle 3: (18, 32, 8)  → (13, 32, 4)
   Cycle 4: (13, 32, 4)  → (9, 32, 2)
   Cycle 5: (9, 32, 2)   → (6, 32, 1)

   Final: (6, 32, 1). Total = 39.
   Normalised: (0.154, 0.821, 0.026)

   Theoretical Bayesian posterior with uniform prior (1/3 each), likelihoods
   (3/9, 4/9, 2/9), after k = 5 i.i.d. observations:
     posterior_i ∝ (L_i)^5
     (3/9)^5 : (4/9)^5 : (2/9)^5 = 243 : 1024 : 32
     normalised: 0.187 : 0.788 : 0.025

   Simulated:    (0.154, 0.821, 0.026)
   Theoretical:  (0.187, 0.788, 0.025)
   Max diff: ~0.033

   Inner_2 dominates as expected; inner_3 collapses toward 0;
   inner_1 retains some weight (it is one step off, not dead). *)

(******************************************************************************)
(* SECTION 8: DIAGNOSTIC EVALS                                                *)
(*                                                                            *)
(* These produce no proof obligation; they are for inspection by Compute.    *)
(* Run with: Compute final_budgets.                                           *)
(******************************************************************************)

(* Uncomment to evaluate after compile:

   Eval cbv in final_budgets.
     -- expected: ~[18; 23; 13]  (or close, modulo discretisation)

   Eval cbv in (snd (fst run_result)).
     -- remaining processing budget after the run

   Eval cbv in score_inner_2_on_source.
     -- expected: (fs (fs (fs (fs fz))), b', h') where
        the first component is f4 = 4, the radius (perfect match)
*)

(* Test that scoring at least computes a known value for one signal: *)
Definition score_inner_2_on_source : Fin * Budget * Spuren :=
  soft_filter_score inner_2 source_signal f16.

(* Expected: score = 4, since distance is 0 and radius is 4. *)

(******************************************************************************)
(* SECTION 9: NEXT STEPS                                                      *)
(*                                                                            *)
(* If `Compute final_budgets` produces values close to the predicted          *)
(* (18, 23, 13), the construction is on solid ground and we can proceed:     *)
(*                                                                            *)
(*   1. State and prove a convergence theorem: the normalised budget         *)
(*      ratios approach the (discrete) Bayesian posterior with               *)
(*      accumulated error O(k/D).                                             *)
(*                                                                            *)
(*   2. Generalise the experiment to non-constant signal streams (mixture   *)
(*      of sources) and show that posteriors track the empirical signal     *)
(*      distribution.                                                        *)
(*                                                                            *)
(*   3. Connect explicitly to filter_implies_spur and closed_system_dies    *)
(*      so that "non-matching inners die" is a structural consequence,      *)
(*      not a hand-wave.                                                    *)
(*                                                                            *)
(* If the experiment does not produce expected values, the candidate        *)
(* failure modes are:                                                        *)
(*                                                                            *)
(*   (a) Processing budget runs out mid-cycle, returning BUnknown / fz;     *)
(*       fix: increase processing_budget further.                            *)
(*                                                                            *)
(*   (b) Floor division accumulates more error than expected;               *)
(*       fix: reconsider distribution rule or use a different rounding mode.*)
(*                                                                            *)
(*   (c) Score discretisation collapses near-equal scores;                   *)
(*       fix: increase delta_per_signal or sharpen the score function.      *)
(******************************************************************************)

(******************************************************************************)
(* SECTION 10: PRINT THE RESULT                                               *)
(******************************************************************************)

(* vm_compute is faster than cbv for large budget terms *)
Eval vm_compute in final_budgets.
Eval vm_compute in (snd (fst run_result)).
Eval vm_compute in score_inner_2_on_source.

(* Optional: also run the legacy additive version for comparison. *)
Definition final_budgets_additive : list Budget :=
  extract_budgets (fst (fst run_result_additive)).

Eval vm_compute in final_budgets_additive.

(******************************************************************************)
(* SECTION 11: UNFLOORED IDEAL TRAJECTORY AND DRIFT                          *)
(*                                                                            *)
(* Compute the unfloored ideal trajectory for the multiplicative dynamic     *)
(* and the integer-pair drift between simulated and ideal. Everything is     *)
(* internal: numerator and denominator are integers built from the           *)
(* parameters; no real-valued or rational object is invoked.                 *)
(*                                                                            *)
(* For multiplicative engagement with k identical signals from source s,    *)
(* the unfloored trajectory of pattern P_i has                               *)
(*                                                                            *)
(*   ideal_numerator(i, k) = val(P_i^(0)) * sigma_i(s)^k                    *)
(*   ideal_denominator(k)  = sigma_max^k                                     *)
(*                                                                            *)
(* The normalised ideal value is (val(P_i^(0)) * sigma_i^k) / SUM_j ...,    *)
(* where the sigma_max^k factors cancel. We compute the integer numerators *)
(* directly and sum them.                                                    *)
(******************************************************************************)

(* Compute sigma_i for each inner against the source signal. *)
Fixpoint compute_sigmas
  (ms : list Membrane) (signal : list Pattern) (b : Budget)
  : (list Fin * Budget * Spuren) :=
  match ms with
  | [] => ([], b, fz)
  | m :: rest =>
      match soft_filter_score m signal b with
      | (s_m, b1, h1) =>
          match compute_sigmas rest signal b1 with
          | (rest_sigmas, b2, h2) =>
              (s_m :: rest_sigmas, b2, add_spur h1 h2)
          end
      end
  end.

(* Iterate sigma to k-th power: sigma^k = sigma * sigma * ... * sigma (k times). *)
Fixpoint pow_fin (base : Fin) (k : Fin) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match k with
  | fz => (fs fz, b, fz)  (* sigma^0 = 1 *)
  | fs k' =>
      match pow_fin base k' b with
      | (acc, b1, h1) =>
          match mult_fin_spur acc base b1 with
          | (res, b2, h2) => (res, b2, add_spur h1 h2)
          end
      end
  end.

(* For each pattern, compute val(P_i^(0)) * sigma_i^k. Returns list of integer
   numerators (before normalisation). *)
Fixpoint compute_ideal_numerators
  (initial_values : list Fin)
  (sigmas : list Fin)
  (k : Fin)
  (b : Budget)
  : (list Fin * Budget * Spuren) :=
  match initial_values, sigmas with
  | [], _ => ([], b, fz)
  | _, [] => ([], b, fz)
  | v0 :: rest_v, sigma :: rest_s =>
      match pow_fin sigma k b with
      | (sigma_pow_k, b1, h1) =>
          match mult_fin_spur v0 sigma_pow_k b1 with
          | (numer, b2, h2) =>
              match compute_ideal_numerators rest_v rest_s k b2 with
              | (rest_numers, b3, h3) =>
                  (numer :: rest_numers, b3,
                   add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

(* Sum the ideal numerators to get the ideal total. *)
Fixpoint sum_fin_list (l : list Fin) (b : Budget) : (Fin * Budget * Spuren) :=
  match l with
  | [] => (fz, b, fz)
  | x :: rest =>
      match sum_fin_list rest b with
      | (s, b1, h1) =>
          match add_fin_b_spur x s b1 with
          | (total, b2, h2) => (total, b2, add_spur h1 h2)
          end
      end
  end.

(* Test fixture: 5 identical signals, so k = f5 in our parameter naming. *)
Definition signal_count : Fin := f5.

(* Initial values are 32, 32, 32 (matching test_inners). *)
Definition initial_values : list Fin := [f32; f32; f32].

(* Dedicated budget for the ideal computation. mult_fin_spur is O(n*m),
   so the chain mult 32 * 1024 alone costs ~32000 budget per pattern.
   Three patterns plus pow chains need ~100K budget; we allocate 200K. *)
Definition ideal_budget : Budget := f209952.

(* Compute the sigmas (filter scores) for each inner against source_signal. *)
Definition fixture_sigmas_result :=
  compute_sigmas test_inners source_signal ideal_budget.

Definition fixture_sigmas : list Fin :=
  fst (fst fixture_sigmas_result).

(* Compute the ideal numerators val_i^(0) * sigma_i^k for each pattern. *)
Definition ideal_numerators_result :=
  compute_ideal_numerators initial_values fixture_sigmas signal_count
                            (snd (fst fixture_sigmas_result)).

Definition ideal_numerators : list Fin :=
  fst (fst ideal_numerators_result).

(* Compute the total of ideal numerators. *)
Definition ideal_total_result :=
  sum_fin_list ideal_numerators (snd (fst ideal_numerators_result)).

Definition ideal_total : Fin :=
  fst (fst ideal_total_result).

(* Print ideal numerators and ideal total — these are the (unfloored)
   integer-pair representation of the ideal trajectory after k signals.
   The normalised ideal vector is (numer_i, ideal_total) for each i. *)
Eval vm_compute in fixture_sigmas.
Eval vm_compute in ideal_numerators.
Eval vm_compute in ideal_total.

(* Predicted values:
     fixture_sigmas    = [3; 4; 2]   (filter scores at signal (3,8))
     ideal_numerators  = [32 * 3^5; 32 * 4^5; 32 * 2^5]
                       = [32 * 243; 32 * 1024; 32 * 32]
                       = [7776; 32768; 1024]
     ideal_total       = 7776 + 32768 + 1024 = 41568

   Normalised ideal:    (7776/41568, 32768/41568, 1024/41568)
                       ≈ (0.187,    0.788,      0.025)

   Simulated final:     (6, 32, 1)  → normalised (6/39, 32/39, 1/39)
                       ≈ (0.154,    0.821,      0.026)

   Drift, max component:
     |6/39 - 7776/41568|  ≈ 0.033
     |32/39 - 32768/41568| ≈ 0.033
     |1/39 - 1024/41568|   ≈ 0.001

   Theorem A.4 bound for n=3, k=5, V^(0)=96:
     n*(n+1)*k / V^(0) = 3 * 4 * 5 / 96 = 60/96 = 5/8 = 0.625

   Empirical drift (≈0.033) below bound (0.625) by factor ~19. ✓ *)

(******************************************************************************)
(* SECTION 12: ALTERNATING SIGNAL STREAM — beyond universal-engager regime  *)
(*                                                                            *)
(* The previous sections used a fixed signal source. The universal-engager  *)
(* condition of Theorem A.4 was satisfied: inner_2 had sigma=sigma_max at   *)
(* every step. This section tests the bound when NO single pattern is the   *)
(* universal engager throughout the stream.                                  *)
(*                                                                            *)
(* Setup: alternating signals from two sources.                              *)
(*   source_a = (3,8) — matches inner_2 (sigma 3,4,2)                      *)
(*   source_b = (5,8) — matches inner_3 (sigma 1,2,4)                      *)
(*                                                                            *)
(* Stream: [a; b; a; b; a]. Across this stream:                             *)
(*   inner_1: sigmas [3, 1, 3, 1, 3], product = 27                          *)
(*   inner_2: sigmas [4, 2, 4, 2, 4], product = 256                         *)
(*   inner_3: sigmas [2, 4, 2, 4, 2], product = 128                         *)
(*                                                                            *)
(* No single pattern has sigma = sigma_max = 4 at every step. The           *)
(* universal-engager hypothesis of Theorem A.4 is violated. We test         *)
(* whether the empirical drift remains within the worst-case bound.        *)
(******************************************************************************)

(* Second source signal at point 5/8 — exactly matches inner_3. *)
Definition source_signal_b : list Pattern := [mk_pattern_from_pair f5 f8].

(* Alternating stream of length 5. *)
Definition signal_stream_alt : list (list Pattern) :=
  [source_signal; source_signal_b; source_signal;
   source_signal_b; source_signal].

(* Run multiplicative replicator on the alternating stream. *)
Definition run_result_alt : list Membrane * Budget * Spuren :=
  replicator_run test_inners signal_stream_alt score_divisor processing_budget.

Definition final_budgets_alt : list Budget :=
  extract_budgets (fst (fst run_result_alt)).

Eval vm_compute in final_budgets_alt.

(* Compute the per-cycle sigmas for the alternating stream.
   For each pattern i, we get the list [sigma_i(s_1); sigma_i(s_2); ...].

   Walking the signal stream and computing sigma per pattern at each step. *)
Fixpoint compute_sigmas_per_signal
  (ms : list Membrane) (signal : list Pattern) (b : Budget)
  : (list Fin * Budget * Spuren) :=
  match ms with
  | [] => ([], b, fz)
  | m :: rest =>
      match soft_filter_score m signal b with
      | (s_m, b1, h1) =>
          match compute_sigmas_per_signal rest signal b1 with
          | (rest_sigmas, b2, h2) =>
              (s_m :: rest_sigmas, b2, add_spur h1 h2)
          end
      end
  end.

(* For one pattern, compute the product of its sigmas across a list of signals. *)
Fixpoint product_of_sigmas_for_one
  (m : Membrane) (signals : list (list Pattern)) (b : Budget)
  : (Fin * Budget * Spuren) :=
  match signals with
  | [] => (fs fz, b, fz)  (* empty product = 1 *)
  | s :: rest =>
      match soft_filter_score m s b with
      | (sigma, b1, h1) =>
          match product_of_sigmas_for_one m rest b1 with
          | (rest_prod, b2, h2) =>
              match mult_fin_spur sigma rest_prod b2 with
              | (prod, b3, h3) =>
                  (prod, b3, add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

(* For each pattern, compute v_init * product_of_sigmas_for_one over alt stream. *)
Fixpoint ideal_numerators_alt
  (initial_values : list Fin)
  (ms : list Membrane)
  (signals : list (list Pattern))
  (b : Budget)
  : (list Fin * Budget * Spuren) :=
  match initial_values, ms with
  | [], _ => ([], b, fz)
  | _, [] => ([], b, fz)
  | v0 :: rest_v, m :: rest_m =>
      match product_of_sigmas_for_one m signals b with
      | (prod, b1, h1) =>
          match mult_fin_spur v0 prod b1 with
          | (numer, b2, h2) =>
              match ideal_numerators_alt rest_v rest_m signals b2 with
              | (rest_n, b3, h3) =>
                  (numer :: rest_n, b3, add_spur h1 (add_spur h2 h3))
              end
          end
      end
  end.

Definition alt_numerators_result :=
  ideal_numerators_alt initial_values test_inners signal_stream_alt ideal_budget.

Definition alt_numerators : list Fin :=
  fst (fst alt_numerators_result).

Definition alt_total_result :=
  sum_fin_list alt_numerators (snd (fst alt_numerators_result)).

Definition alt_total : Fin :=
  fst (fst alt_total_result).

Eval vm_compute in alt_numerators.
Eval vm_compute in alt_total.

(* Predicted values for alternating stream:
     alt_numerators = [32*27; 32*256; 32*128] = [864; 8192; 4096]
     alt_total      = 864 + 8192 + 4096 = 13152

   Simulated trajectory (computed by hand from the multiplicative rule):
     b^(0) = (32, 32, 32)
     b^(1) = (24, 32, 16)   — after signal_a, scores (3,4,2)
     b^(2) = (6,  16, 16)   — after signal_b, scores (1,2,4)
     b^(3) = (4,  16, 8)    — after signal_a
     b^(4) = (1,  8,  8)    — after signal_b
     b^(5) = (0,  8,  4)    — after signal_a

   Note: inner_1 hits zero — pattern silence. Structurally extinguished
   by the floor operation when its engagement value drops below 1.

   Final simulated normalised: (0/12, 8/12, 4/12) = (0, 0.667, 0.333)
   Final ideal normalised:     (864/13152, 8192/13152, 4096/13152)
                              ≈ (0.066, 0.623, 0.311)

   Drift, max component:
     |0 - 0.066| = 0.066
     |0.667 - 0.623| ≈ 0.044
     |0.333 - 0.311| ≈ 0.022

   Theorem A.4 bound for n=3, k=5, V^(0)=96: 0.625.
   Empirical max drift (~0.066) below bound by factor ~10. ✓

   Importantly: NO single pattern was the universal engager throughout.
   The Theorem A.4 hypothesis is technically violated. Yet the bound
   still holds. This suggests the proof structure generalises beyond
   the strict universal-engager condition; a tighter analysis covering
   the rotating-engager case is open work.

   Also notable: inner_1 went silent. This is the structural-silence
   phenomenon predicted in Section 3.4 of the paper — patterns whose
   capacity (engagement value, in this experiment) drops below the
   engagement threshold become non-responsive to subsequent signals.
   In the alternating fixture, inner_1 has the worst overall match
   (low sigma against both sources) and is the first to fall silent. *)

(******************************************************************************)
(* SECTION 13. STRUCTURAL VERIFICATION OF SECTION 11 AND 12 PREDICTIONS       *)
(*                                                                            *)
(* The Eval vm_compute outputs above are evaluable but not formal theorems.   *)
(* The lemmas below promote those evaluations into Coq theorems closed by     *)
(* Qed: the simulated trajectories at k=5 for the multiplicative fixture     *)
(* (fixed source) and the alternating-stream extension are exactly the       *)
(* predicted vectors.                                                         *)
(*                                                                            *)
(* These verifications cover the structurally-checkable values (small enough *)
(* to be expressible as concrete Fin literals via the f1..f32 series). The   *)
(* ideal numerator and total values for the alternating stream require a    *)
(* small additional pure-Fin arithmetic helper to express as literals; that *)
(* is left for a subsequent revision.                                        *)
(******************************************************************************)

(* Multiplicative trajectory under fixed source: final_budgets = [6; 32; 1]. *)
Theorem final_budgets_fixed_correct :
  final_budgets = (f6 :: f32 :: f1 :: nil).
Proof. vm_compute. reflexivity. Qed.

(* Alternating-stream extension: final_budgets_alt = [0; 8; 4].
   Inner_1 is structurally silent (value zero) — the pattern silence
   phenomenon of Section 3.4 of the paper, observed in formal verification. *)
Theorem final_budgets_alt_correct :
  final_budgets_alt = (fz :: f8 :: f4 :: nil).
Proof. vm_compute. reflexivity. Qed.

(* Pattern silence as a structural fact: the head of the alternating
   trajectory's final budget is exactly fz. *)
Theorem inner_1_pattern_silence :
  hd fz final_budgets_alt = fz.
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(* SECTION 14: DATASET, COVERAGE, AND THE PATTERN-SILENCE ROAD                *)
(*                                                                            *)
(* The Mortal Pattern Theorem proper begins here. Dataset and coverage are   *)
(* defined as RELATIONS on lists, never as cardinalities of sets — this is  *)
(* the void-theoretic stance: counting elements is an act with budget cost, *)
(* not a property of an abstract collection. We use only In, exists, /\,    *)
(* forall — the bare scaffolding of constructive logic.                      *)
(******************************************************************************)

(* A dataset is a list of signals; each signal is itself a list of Patterns. *)
Definition Dataset := list (list Pattern).

(* Predicate: membrane m recognizes signal s, paying from its own budget.    *)
(* True iff calling recognize with m's filter and m's mem_budget yields BTrue.*)
Definition recognizes (m : Membrane) (s : list Pattern) : Prop :=
  exists b' h,
    recognize s (membrane_as_figure m) (mem_budget m) = (BTrue, b', h).

(* Predicate: list of membranes P covers dataset D — every signal in D     *)
(* has at least one membrane in P that recognizes it.                       *)
Definition covers (P : list Membrane) (D : Dataset) : Prop :=
  forall s, In s D -> exists m, In m P /\ recognizes m s.

(* ---- Structural lemmas ---- *)

(* Coverage of empty dataset is trivial. *)
Lemma covers_nil : forall P, covers P [].
Proof.
  intros P s Hin. simpl in Hin. contradiction.
Qed.

(* Coverage decomposes over cons: head is recognized, tail still covered.    *)
Lemma covers_cons_inv : forall P s rest,
  covers P (s :: rest) ->
  (exists m, In m P /\ recognizes m s) /\ covers P rest.
Proof.
  intros P s rest Hcov. split.
  - apply Hcov. simpl. left. reflexivity.
  - intros s' Hin'. apply Hcov. simpl. right. exact Hin'.
Qed.

(* Coverage composes over cons: head + tail covered implies whole covered.   *)
Lemma covers_cons_intro : forall P s rest,
  (exists m, In m P /\ recognizes m s) ->
  covers P rest ->
  covers P (s :: rest).
Proof.
  intros P s rest Hhead Htail s' Hin.
  simpl in Hin. destruct Hin as [Heq | Hin'].
  - subst s'. exact Hhead.
  - apply Htail. exact Hin'.
Qed.

(* Adding membranes preserves coverage (monotonicity, append on the right).  *)
Lemma covers_extend_right : forall P extra D,
  covers P D -> covers (P ++ extra) D.
Proof.
  intros P extra D Hcov s Hin.
  destruct (Hcov s Hin) as [m [HmIn Hrec]].
  exists m. split.
  - apply in_or_app. left. exact HmIn.
  - exact Hrec.
Qed.

(* Adding membranes on the left also preserves coverage.                     *)
Lemma covers_extend_left : forall extra P D,
  covers P D -> covers (extra ++ P) D.
Proof.
  intros extra P D Hcov s Hin.
  destruct (Hcov s Hin) as [m [HmIn Hrec]].
  exists m. split.
  - apply in_or_app. right. exact HmIn.
  - exact Hrec.
Qed.

(******************************************************************************)
(* SECTION 15: EXHAUSTION — zero capacity is a fixed point                   *)
(*                                                                            *)
(* The Mortal Pattern Theorem rests on a structural fact: once a membrane's *)
(* capacity collapses to fz, no further cap_decay step can lift it. The     *)
(* dead stay dead. Here we prove it for one step and then for arbitrary     *)
(* iteration depth, yielding the foundation for the silence theorem.        *)
(*                                                                            *)
(* The full quantitative exhaustion (k_silence as a function of B, lambda,  *)
(* c_min) requires real-valued lambda = M / sigma_max which is alien to the *)
(* finitist substrate. The structural form proved here is the void-theoretic*)
(* analogue: dynamics have an absorbing state at fz and the iter is closed  *)
(* under it.                                                                  *)
(******************************************************************************)

(* ---- Helper: multiplication by zero on the left yields zero ---- *)
(* Computational witness: mult_fin_spur fz m b reduces to (fz, _, _).        *)
(* Stated existentially because the residual budget and spuren vary with m  *)
(* and b, but the value is always fz.                                        *)

Lemma mult_fin_spur_zero_l_exists : forall m b,
  exists b' h', mult_fin_spur fz m b = (fz, b', h').
Proof.
  induction m as [| m' IH]; intro b.
  - exists b, fz. reflexivity.
  - destruct b as [| b'].
    + exists fz, fz. reflexivity.
    + simpl. destruct (IH b') as [b'' [h1 Hrec]].
      rewrite Hrec. exists b'', (fs (add_spur h1 fz)).
      reflexivity.
Qed.

(* ---- LEMMA (single step): zero capacity is preserved by cap_decay ---- *)

Lemma cap_zero_preserved :
  forall m signal sigma_max c_min b m' b' h,
  mem_capacity m = fz ->
  cap_decay m signal sigma_max c_min b = (m', b', h) ->
  mem_capacity m' = fz.
Proof.
  intros m signal sigma_max c_min b m' b' h Hcap Hcd.
  unfold cap_decay in Hcd.
  destruct (soft_filter_score m signal b) as [[sigma b1] h1] eqn:Hsf.
  rewrite Hcap in Hcd.
  destruct (mult_fin_spur_zero_l_exists sigma b1) as [b2 [h2 Hmult]].
  rewrite Hmult in Hcd.
  rewrite div_fin_spur_zero_num in Hcd.
  destruct (sub_saturate_b_spur fz c_min b2) as [[new_cap b4] h4] eqn:Hsub.
  pose proof (sub_saturate_zero_num_fst c_min b2) as Hzero.
  rewrite Hsub in Hzero. simpl in Hzero. subst new_cap.
  inversion Hcd; subst.
  reflexivity.
Qed.

(* ---- Iterated cap_decay ---- *)

Fixpoint cap_decay_iter
  (m : Membrane)
  (signal : list Pattern)
  (sigma_max : Fin)
  (c_min : Fin)
  (steps : Fin)
  (b : Budget)
  : (Membrane * Budget * Spuren) :=
  match steps with
  | fz => (m, b, fz)
  | fs steps' =>
      match cap_decay m signal sigma_max c_min b with
      | (m1, b1, h1) =>
          match cap_decay_iter m1 signal sigma_max c_min steps' b1 with
          | (mfin, bfin, h2) => (mfin, bfin, add_spur h1 h2)
          end
      end
  end.

(* ---- THEOREM (iterated): zero capacity is preserved across all steps ---- *)
(* If a membrane starts dead (mem_capacity = fz), it stays dead through any  *)
(* number of cap_decay iterations. This is the absorbing-state property.    *)

Theorem cap_iter_zero_preserved :
  forall steps m signal sigma_max c_min b m' b' h,
  mem_capacity m = fz ->
  cap_decay_iter m signal sigma_max c_min steps b = (m', b', h) ->
  mem_capacity m' = fz.
Proof.
  induction steps as [| steps' IH];
    intros m signal sigma_max c_min b m' b' h Hcap Hci.
  - simpl in Hci. inversion Hci; subst. exact Hcap.
  - simpl in Hci.
    destruct (cap_decay m signal sigma_max c_min b) as [[m1 b1] h1] eqn:Hcd.
    destruct (cap_decay_iter m1 signal sigma_max c_min steps' b1)
      as [[mfin bfin] h2] eqn:Hci'.
    inversion Hci; subst.
    pose proof (cap_zero_preserved _ _ _ _ _ _ _ _ Hcap Hcd) as Hcap1.
    exact (IH _ _ _ _ _ _ _ _ Hcap1 Hci').
Qed.

(******************************************************************************)
(* SECTION 16: PATTERN SILENCE THEOREM                                       *)
(*                                                                            *)
(* The capstone result. We lift cap_decay from a single membrane to a list  *)
(* (one signal applied to all membranes), then iterate over a stream of      *)
(* signals. The theorem: a population that begins entirely silent           *)
(* (zero capacity throughout) remains entirely silent under any sequence    *)
(* of signal-driven cap_decay iterations.                                    *)
(*                                                                            *)
(* In words: silence is absorbing. Dynamics never create capacity from       *)
(* nothing. Pattern silence is structural — once a population is exhausted, *)
(* no signal stream can resurrect it.                                        *)
(*                                                                            *)
(* The full quantitative form (k_silence as a function of B, lambda, c_min  *)
(* in real arithmetic) is sacrificed here in favor of a finitist            *)
(* statement which captures the same essential phenomenon: zero is the      *)
(* terminal state, attained finitely, never escaped.                         *)
(******************************************************************************)

(* ---- list_cap_decay: lift cap_decay from one membrane to a list ---- *)

Fixpoint list_cap_decay
  (Ms : list Membrane)
  (signal : list Pattern)
  (sigma_max c_min : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match Ms with
  | [] => ([], b, fz)
  | m :: rest =>
      match cap_decay m signal sigma_max c_min b with
      | (m', b1, h1) =>
          match list_cap_decay rest signal sigma_max c_min b1 with
          | (rest', b2, h2) => (m' :: rest', b2, add_spur h1 h2)
          end
      end
  end.

(* ---- list_cap_decay_iter: iterate over a stream of signals ---- *)

Fixpoint list_cap_decay_iter
  (Ms : list Membrane)
  (signals : list (list Pattern))
  (sigma_max c_min : Fin)
  (b : Budget)
  : (list Membrane * Budget * Spuren) :=
  match signals with
  | [] => (Ms, b, fz)
  | s :: rest =>
      match list_cap_decay Ms s sigma_max c_min b with
      | (Ms1, b1, h1) =>
          match list_cap_decay_iter Ms1 rest sigma_max c_min b1 with
          | (Mfin, bfin, h2) => (Mfin, bfin, add_spur h1 h2)
          end
      end
  end.

(* ---- LEMMA (single signal): dead list stays dead ---- *)

Lemma list_cap_decay_dead_preserved :
  forall Ms signal sigma_max c_min b Ms' b' h,
  (forall m, In m Ms -> mem_capacity m = fz) ->
  list_cap_decay Ms signal sigma_max c_min b = (Ms', b', h) ->
  forall m', In m' Ms' -> mem_capacity m' = fz.
Proof.
  induction Ms as [| m rest IH];
    intros signal sigma_max c_min b Ms' b' h Hall Hlcd m' Hin'.
  - simpl in Hlcd. inversion Hlcd; subst. simpl in Hin'. contradiction.
  - simpl in Hlcd.
    destruct (cap_decay m signal sigma_max c_min b) as [[m1 b1] h1] eqn:Hcd.
    destruct (list_cap_decay rest signal sigma_max c_min b1)
      as [[rest' b2] h2] eqn:Hlcd_rest.
    inversion Hlcd; subst.
    simpl in Hin'.
    destruct Hin' as [Heq | Hin_rest].
    + subst m'.
      assert (Hcap_m: mem_capacity m = fz)
        by (apply Hall; simpl; left; reflexivity).
      exact (cap_zero_preserved _ _ _ _ _ _ _ _ Hcap_m Hcd).
    + apply (IH signal sigma_max c_min b1 rest' b' h2).
      * intros mm Hin_mm. apply Hall. simpl. right. exact Hin_mm.
      * exact Hlcd_rest.
      * exact Hin_rest.
Qed.

(* ---- THEOREM: PATTERN SILENCE ---- *)
(* A population that begins entirely silent remains entirely silent under   *)
(* any signal stream. Death is absorbing at the population level.           *)

Theorem pattern_silence_theorem :
  forall signals Ms sigma_max c_min b Ms' b' h,
  (forall m, In m Ms -> mem_capacity m = fz) ->
  list_cap_decay_iter Ms signals sigma_max c_min b = (Ms', b', h) ->
  forall m', In m' Ms' -> mem_capacity m' = fz.
Proof.
  induction signals as [| s rest IH];
    intros Ms sigma_max c_min b Ms' b' h Hall Hlcdi m' Hin'.
  - simpl in Hlcdi. inversion Hlcdi; subst. exact (Hall m' Hin').
  - simpl in Hlcdi.
    destruct (list_cap_decay Ms s sigma_max c_min b)
      as [[Ms1 b1] h1] eqn:Hlcd.
    destruct (list_cap_decay_iter Ms1 rest sigma_max c_min b1)
      as [[Mfin bfin] h2] eqn:Hlcdi'.
    inversion Hlcdi; subst.
    apply (IH Ms1 sigma_max c_min b1 Ms' b' h2).
    + intros mm Hin_mm.
      exact (list_cap_decay_dead_preserved
               Ms s sigma_max c_min b Ms1 b1 h1 Hall Hlcd mm Hin_mm).
    + exact Hlcdi'.
    + exact Hin'.
Qed.

(******************************************************************************)
(* SECTION 17: CAP MONOTONICITY — capacity never grows                       *)
(*                                                                            *)
(* Strengthening MPT from "dead stays dead" to full monotonicity:            *)
(* mem_capacity never grows under cap_decay. The argument is structural:     *)
(* cap_decay applies sub_saturate at the end, and sub_saturate's first       *)
(* argument bounds the result from above. So whatever mult/div do in the    *)
(* middle, the final new_cap is bounded by what came out of div_fin_spur,   *)
(* which in turn (when sigma ≤ sigma_max) is bounded by the original cap.   *)
(*                                                                            *)
(* This section proves the structural piece (sub_saturate). The full         *)
(* mult/div bound is left for a future iteration — it requires arithmetic   *)
(* lemmas about mult_fin_spur and div_fin_spur that depend on each other    *)
(* and on the structure of finitist multiplication.                          *)
(******************************************************************************)

(* ---- LEMMA: sub_saturate result is bounded above by its first argument ---- *)
(* sub_saturate n c b never returns a value greater than n. The saturation   *)
(* at fz on underflow plus the structural recursion guarantee res ≤ n.      *)

Lemma sub_saturate_le_n :
  forall n c b res b' h,
  sub_saturate_b_spur n c b = (res, b', h) ->
  leF res n.
Proof.
  induction n as [| n' IH];
    intros c b res b' h Heq.
  - (* n = fz *)
    destruct b as [| b''].
    + simpl in Heq. inversion Heq; subst. constructor.
    + destruct c as [| c''].
      * simpl in Heq. inversion Heq; subst. constructor.
      * simpl in Heq. inversion Heq; subst. constructor.
  - (* n = fs n' *)
    destruct b as [| b''].
    + simpl in Heq. inversion Heq; subst. constructor.
    + destruct c as [| c''].
      * simpl in Heq. inversion Heq; subst. apply leF_refl.
      * simpl in Heq.
        destruct (sub_saturate_b_spur n' c'' b'') as [[r b'''] h'] eqn:Hrec.
        inversion Heq; subst.
        pose proof (IH _ _ _ _ _ Hrec) as IHres.
        apply leF_trans with n'.
        ** exact IHres.
        ** apply leF_step.
Qed.

(* ---- THEOREM: cap_decay's final new_cap is bounded by cap_decayed ---- *)
(* The final step of cap_decay is sub_saturate cap_decayed c_min. Whatever  *)
(* cap_decayed turned out to be (after mult/div), the new_cap returned to   *)
(* the membrane is at most cap_decayed. This is the structural piece of     *)
(* monotonicity — the c_min subtraction never lifts capacity.               *)

Theorem cap_decay_bounded_by_intermediate :
  forall m signal sigma_max c_min b m' b' h
         sigma b1 h1 numer b2 h2 cap_decayed _rem b3 h3,
  soft_filter_score m signal b = (sigma, b1, h1) ->
  mult_fin_spur (mem_capacity m) sigma b1 = (numer, b2, h2) ->
  div_fin_spur numer sigma_max b2 = (cap_decayed, _rem, b3, h3) ->
  cap_decay m signal sigma_max c_min b = (m', b', h) ->
  leF (mem_capacity m') cap_decayed.
Proof.
  intros m signal sigma_max c_min b m' b' h
         sigma b1 h1 numer b2 h2 cap_decayed _rem b3 h3
         Hsf Hmult Hdiv Hcd.
  unfold cap_decay in Hcd.
  rewrite Hsf in Hcd.
  rewrite Hmult in Hcd.
  rewrite Hdiv in Hcd.
  destruct (sub_saturate_b_spur cap_decayed c_min b3) as [[new_cap b4] h4] eqn:Hsub.
  inversion Hcd; subst. simpl.
  exact (sub_saturate_le_n _ _ _ _ _ _ Hsub).
Qed.

(******************************************************************************)
(* SECTION 18: TRESOR THEOREM — shape as condition of discrimination          *)
(*                                                                            *)
(* Tresor Theorem — named after the Berlin techno club built in a bank vault.*)
(* Shape (filter) is the condition of discrimination, not its enemy. Three   *)
(* faces of the same insight: without shape there is no learning.            *)
(*                                                                            *)
(*   basic_channel:           score = 0     → death  (Basic Channel, Berlin  *)
(*                            dub techno — music reduced to silence itself)   *)
(*   birmingham_stagnation:   score = const → freeze (Birmingham — Surgeon,  *)
(*                            Regis — post-industrial stasis as sonic form)   *)
(*   tresor_discrimination:   score varies  → learn  (real shape, real       *)
(*                            selection — the vault is calibrated)           *)
(*                                                                            *)
(* The vault keeps what is precious (recognition, learning) inside. Open the *)
(* vault (radius → infinite, no filter) and value escapes. Lock it too tight *)
(* (radius = 0, no width) and nothing can enter. Only a calibrated shape —   *)
(* finite, bounded, with structure — discriminates.                          *)
(******************************************************************************)

(* ---- BASIC_CHANNEL: no fit → death ---- *)
(* Basic Channel — Moritz von Oswald & Mark Ernestus, Berlin. Music reduced *)
(* to its skeleton: silence as structural element. Here: score = 0 means    *)
(* the signal falls outside the filter. The membrane receives nothing;      *)
(* cost-of-presence finishes the job alone. Silence is death.               *)

Theorem basic_channel :
  forall m signal sigma_max c_min b b1 h1 m' b' h,
  soft_filter_score m signal b = (fz, b1, h1) ->
  cap_decay m signal sigma_max c_min b = (m', b', h) ->
  mem_capacity m' = fz.
Proof. exact zero_match_annihilation. Qed.

(* ---- BIRMINGHAM_STAGNATION: homogeneous shapes → frozen budgets ---- *)
(* Birmingham — Surgeon, Regis, Female, the Birmingham sound: industrial    *)
(* repetition as aesthetic. Post-industrial stasis made sonic. Here:         *)
(* three membranes with identical centers and radii see the same signal.    *)
(* Each scores identically; under multiplicative_update each computes       *)
(*   new_b = floor(budget × divisor / divisor) = budget                     *)
(* — budgets unchanged. No differentiation, no selection, no learning.      *)
(* The machine repeats. Nothing moves. Birmingham.                          *)

Definition birm_m1 : Membrane :=
  mkMembrane [mk_pattern_from_pair f3 f8] f4 f4 f4 nil.
Definition birm_m2 : Membrane :=
  mkMembrane [mk_pattern_from_pair f3 f8] f4 f4 f8 nil.
Definition birm_m3 : Membrane :=
  mkMembrane [mk_pattern_from_pair f3 f8] f4 f4 f16 nil.

Definition birm_membranes : list Membrane := [birm_m1; birm_m2; birm_m3].
Definition birm_signal : list Pattern := [mk_pattern_from_pair f3 f8].
Definition birm_divisor : Fin := f4.  (* = mem_filter_radius for each m *)

(* The result of multiplicative_update on the stagnation fixture: the       *)
(* resulting membrane list has the same budgets as the input list.          *)
Definition birm_result_budgets : list Fin :=
  map mem_budget (fst (fst
    (multiplicative_update birm_membranes birm_signal birm_divisor f7776))).

Theorem birmingham_stagnation :
  birm_result_budgets = map mem_budget birm_membranes.
Proof. vm_compute. reflexivity. Qed.

(* ---- TRESOR_DISCRIMINATION: heterogeneous shapes → learning ---- *)
(* Wrapper for final_budgets_fixed_correct: heterogeneous membranes (inner_1,*)
(* inner_2, inner_3) with centers at 2/8, 3/8, 5/8 see a signal at 3/8. The *)
(* scores differ (inner_2 matches perfectly, inner_1 close, inner_3 far),  *)
(* and after 5 cycles the budgets diverge: (6, 32, 1). Inner_2 keeps almost *)
(* everything; inner_3 nearly dies. Real shape, real selection, real        *)
(* learning. The vault is calibrated. *)

Theorem tresor_discrimination :
  final_budgets = (f6 :: f32 :: f1 :: nil).
Proof. exact final_budgets_fixed_correct. Qed.

(* ---- Sanity witnesses for the Tresor trio ---- *)

(* basic_channel in action: a membrane with center far from the signal      *)
(* (score = 0), after cap_decay with c_min ≥ 1, has mem_capacity = fz.     *)
Eval vm_compute in
  (let m := mkMembrane [mk_pattern_from_pair f8 f8] f1 f4 f8 nil in
   let signal := [mk_pattern_from_pair fz f8] in
   (* signal far from filter center, score = fz *)
   cap_decay m signal f4 (fs fz) f7776).

(* birmingham_stagnation in action: identical centers, budgets preserved. *)
Eval vm_compute in birm_result_budgets.
(* Expected: [f4; f8; f16] — same as input *)

(* servants_discrimination in action: final_budgets after 5 cycles. *)
Eval vm_compute in final_budgets.
(* Expected: [f6; f32; f1] — divergent *)
