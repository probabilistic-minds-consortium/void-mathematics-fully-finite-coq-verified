(******************************************************************************)
(* void_geometry_distinguishability.v                                        *)
(* BRIDGE: Geometry sees through Distinguishability                          *)
(*                                                                           *)
(* void_geometry.v computes vector distance using numerators only.           *)
(* void_distinguishability.v computes proper fraction differences.           *)
(* This module connects them: geometric distance IS distinguishability.      *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import void_geometry.
Require Import void_distinguishability.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Geometry_Distinguishability.

Import Void_Geometry.
Import Void_Distinguishability.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* PROPER FRACTION DISTANCE — uses prob_diff, not numerator subtraction      *)
(******************************************************************************)

(* Component difference via proper fraction arithmetic.
   prob_diff_with_budget cross-multiplies to common denominator,
   then subtracts. This respects the full FinProb, not just fst. *)
Definition component_diff_b (p1 p2 : FinProb) (b : Budget) 
  : (FinProb * Budget) :=
  prob_diff_with_budget p1 p2 b.

(* Distance between two VoidVectors: sum of component-wise prob_diffs.
   Each component costs one tick for the fold, plus budget for prob_diff.
   Returns the accumulated numerator as Fin — the total separation. *)
Fixpoint vector_prob_distance_b (v1 v2 : VoidVector) (b : Budget) 
  : (Fin * Budget) :=
  match v1, v2, b with
  | [], _, _ => (fz, b)
  | _, [], _ => (fz, b)
  | _, _, fz => (fz, fz)
  | p1 :: rest1, p2 :: rest2, fs b' =>
      match component_diff_b p1 p2 b' with
      | (diff, b1) =>
          match vector_prob_distance_b rest1 rest2 b1 with
          | (rest_dist, b2) =>
              add_fin (fst diff) rest_dist b2
          end
      end
  end.

(******************************************************************************)
(* COMPONENT DISTINGUISHABILITY — which dimensions can be told apart?        *)
(******************************************************************************)

(* For a given threshold, check one component pair.
   Uses exceeds_threshold_with_budget from distinguishability. *)
Definition component_distinguishable_b (p1 p2 : FinProb) 
                                        (threshold : FinProb) (b : Budget)
  : (bool * Budget) :=
  match b with
  | fz => (false, fz)
  | fs b' =>
      match component_diff_b p1 p2 b' with
      | (diff, b1) =>
          exceeds_threshold_with_budget diff threshold b1
      end
  end.

(* Count how many components are distinguishable. One tick per component. *)
Fixpoint distinguishable_components_b (v1 v2 : VoidVector) 
                                       (threshold : FinProb) (b : Budget) 
  : (Fin * Budget) :=
  match v1, v2, b with
  | [], _, _ => (fz, b)
  | _, [], _ => (fz, b)
  | _, _, fz => (fz, fz)
  | p1 :: rest1, p2 :: rest2, fs b' =>
      match component_distinguishable_b p1 p2 threshold b' with
      | (true, b1) =>
          match distinguishable_components_b rest1 rest2 threshold b1 with
          | (count, b2) =>
              match add_fin count operation_cost b2 with
              | (new_count, b3) => (new_count, b3)
              end
          end
      | (false, b1) =>
          distinguishable_components_b rest1 rest2 threshold b1
      end
  end.

(******************************************************************************)
(* DISTINGUISHABILITY DISTANCE — how many dimensions separate two vectors?   *)
(******************************************************************************)

(* The distinguishability distance between two vectors:
   (distinguishable_components, total_components) as FinProb.
   
   This IS the distance in VOID geometry:
   - (0, n) = identical (no dimension can tell them apart)
   - (n, n) = maximally separated (every dimension differs)
   - (k, n) = partially separated (k of n dimensions differ)
   
   Costs: one tick per component for counting + one tick per component
   for distinguishability check. *)
Definition distinguishability_distance_b (v1 v2 : VoidVector) 
                                          (threshold : FinProb) (b : Budget) 
  : (FinProb * Budget) :=
  match b with
  | fz => ((fz, fs fz), fz)
  | fs b' =>
      match distinguishable_components_b v1 v2 threshold b' with
      | (dist_count, b1) =>
          match dimension_with_budget v1 b1 with
          | (dim, b2) =>
              match dim with
              | fz => ((fz, fs fz), b2)    (* empty vectors: 0/1 *)
              | fs d => ((dist_count, fs d), b2)
              end
          end
      end
  end.

(******************************************************************************)
(* VECTOR COMPARISON — are two vectors the same shape?                       *)
(******************************************************************************)

(* Two vectors are indistinguishable if no component exceeds threshold.
   This is cheaper than computing full distance — stops at first
   distinguishable component. *)
Fixpoint vectors_indistinguishable_b (v1 v2 : VoidVector) 
                                      (threshold : FinProb) (b : Budget)
  : (bool * Budget) :=
  match v1, v2, b with
  | [], [], _ => (true, b)
  | [], _, _ => (false, b)     (* different lengths *)
  | _, [], _ => (false, b)
  | _, _, fz => (false, fz)    (* can't determine: report false *)
  | p1 :: rest1, p2 :: rest2, fs b' =>
      match component_distinguishable_b p1 p2 threshold b' with
      | (true, b1) => (false, b1)  (* found difference: stop early *)
      | (false, b1) =>
          vectors_indistinguishable_b rest1 rest2 threshold b1
      end
  end.

(******************************************************************************)
(* NEAREST VECTOR — find the closest in a list                               *)
(******************************************************************************)

(* Among a list of vectors, find the one with fewest distinguishable
   components from the target. Costs budget per vector per component. *)
Fixpoint nearest_vector_b (target : VoidVector) (candidates : list VoidVector)
                           (threshold : FinProb) (b : Budget)
  : (option VoidVector * Budget) :=
  match candidates, b with
  | [], _ => (None, b)
  | _, fz => (None, fz)
  | [v], fs b' =>
      (Some v, b')  (* one candidate: return it, costs one tick *)
  | v :: rest, fs b' =>
      match distinguishable_components_b target v threshold b' with
      | (d_v, b1) =>
          match nearest_vector_b target rest threshold b1 with
          | (None, b2) => (Some v, b2)
          | (Some best, b2) =>
              match distinguishable_components_b target best threshold b2 with
              | (d_best, b3) =>
                  match le_fin_b d_v d_best b3 with
                  | (true, b4) => (Some v, b4)    (* v is closer *)
                  | (false, b4) => (Some best, b4) (* best stays *)
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition vector_prob_distance_ext := vector_prob_distance_b.
Definition distinguishable_components_ext := distinguishable_components_b.
Definition distinguishability_distance_ext := distinguishability_distance_b.
Definition vectors_indistinguishable_ext := vectors_indistinguishable_b.
Definition nearest_vector_ext := nearest_vector_b.

End Void_Geometry_Distinguishability.

(******************************************************************************)
(* WHY THIS BRIDGE EXISTS                                                     *)
(*                                                                            *)
(* void_geometry.v has vector_distance_b. It computes distance by taking     *)
(* dist_fin_b on NUMERATORS ONLY:                                            *)
(*                                                                            *)
(*   dist_fin_b (fst p1) (fst p2)                                           *)
(*                                                                            *)
(* This ignores denominators. (3/4) and (3/8) have distance 0.              *)
(*                                                                            *)
(* void_distinguishability.v has prob_diff_with_budget. It cross-multiplies  *)
(* to common denominator, then subtracts. Proper fraction arithmetic.        *)
(*                                                                            *)
(* This module makes geometry use distinguishability:                         *)
(* - vector_prob_distance_b: total separation via proper fraction diff       *)
(* - distinguishable_components_b: how many dimensions differ                *)
(* - distinguishability_distance_b: (differing, total) as FinProb           *)
(* - vectors_indistinguishable_b: early-exit identity check                  *)
(* - nearest_vector_b: find closest vector in a list                         *)
(*                                                                            *)
(* One tick per component. One tick per operation. No existing code changed. *)
(******************************************************************************)