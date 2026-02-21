(******************************************************************************)
(* void_calculus_geometry_bridge.v                                           *)
(* BRIDGE: Functions live in geometric space                                 *)
(*                                                                           *)
(* void_calculus.v has DiscreteFunction = list of (x, f(x)) pairs.          *)
(* void_geometry.v has VoidVector = list of FinProb.                         *)
(* Both are lists of (Fin * Fin). This module converts between them         *)
(* so geometric operations (distance, projection) work on functions.         *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import void_calculus.
Require Import void_geometry.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Calculus_Geometry_Bridge.

Import Void_Calculus.
Import Void_Geometry.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* FUNCTION → VECTOR — extract shape of function as VoidVector               *)
(******************************************************************************)

(* Extract y-values from sample points, pair each with a scale denominator.
   scale is the "universe size" — what the values are measured against.
   Each y becomes (y, scale) as FinProb. One tick per point. *)
Fixpoint function_to_vector_b (points : list (Fin * Fin)) (scale : Fin) 
                               (b : Budget)
  : (VoidVector * Budget) :=
  match points, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | (_, y) :: rest, fs b' =>
      match function_to_vector_b rest scale b' with
      | (vec, b1) => ((y, scale) :: vec, b1)
      end
  end.

(* Convert a DiscreteFunction to VoidVector. Scale is a parameter —
   caller decides the denominator. *)
Definition discrete_to_vector_b (f : DiscreteFunction) (scale : Fin) 
                                 (b : Budget)
  : (BudgetedVector * Budget) :=
  match function_to_vector_b (sample_points f) scale b with
  | (vec, b1) => ({| vector := vec; vec_budget := b1 |}, b1)
  end.

(******************************************************************************)
(* VECTOR → FUNCTION — interpret vector as function samples                  *)
(******************************************************************************)

(* Convert VoidVector back to sample points. Index becomes x,
   numerator becomes y. One tick per component. *)
Fixpoint vector_to_points_b (vec : VoidVector) (index : Fin) (b : Budget)
  : (list (Fin * Fin) * Budget) :=
  match vec, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | (y, _) :: rest, fs b' =>
      match safe_succ_b index b' with
      | (next_index, b1) =>
          match vector_to_points_b rest next_index b1 with
          | (points, b2) => ((index, y) :: points, b2)
          end
      end
  end.

Definition vector_to_discrete_b (vec : VoidVector) (b : Budget)
  : (DiscreteFunction * Budget) :=
  match vector_to_points_b vec fz b with
  | (points, b1) =>
      ({| sample_points := points;
          resolution_cost := operation_cost |}, b1)
  end.

(******************************************************************************)
(* FUNCTION DISTANCE — how different are two functions?                       *)
(******************************************************************************)

(* Distance between two functions: convert both to vectors, then use
   vector_distance_b from geometry. Same scale for both. *)
Definition function_distance_b (f1 f2 : DiscreteFunction) (scale : Fin)
                                (b : Budget)
  : (Fin * Budget) :=
  match function_to_vector_b (sample_points f1) scale b with
  | (vec1, b1) =>
      match function_to_vector_b (sample_points f2) scale b1 with
      | (vec2, b2) =>
          vector_distance_b vec1 vec2 b2
      end
  end.

(******************************************************************************)
(* DERIVATIVE AS VECTOR — shape of a function's rate of change               *)
(******************************************************************************)

(* Compute derivative at each sample point, collect as VoidVector.
   Each derivative value paired with scale. One tick per point
   plus derivative cost per point. *)
Fixpoint derivative_vector_b (f : DiscreteFunction) 
                              (points : list (Fin * Fin))
                              (scale : Fin) (b : Budget)
  : (VoidVector * Budget) :=
  match points, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | (x, _) :: rest, fs b' =>
      match void_derivative_b f x b' with
      | (slope, b1) =>
          match derivative_vector_b f rest scale b1 with
          | (vec, b2) => ((slope, scale) :: vec, b2)
          end
      end
  end.

(* Full derivative shape of a function as BudgetedVector. *)
Definition derivative_shape_b (f : DiscreteFunction) (scale : Fin) 
                               (b : Budget)
  : (BudgetedVector * Budget) :=
  match derivative_vector_b f (sample_points f) scale b with
  | (vec, b1) => ({| vector := vec; vec_budget := b1 |}, b1)
  end.

(******************************************************************************)
(* FUNCTION SIMILARITY — are two functions the same shape?                   *)
(******************************************************************************)

(* Two functions are similar if their vectors are near each other.
   Uses near_void_b logic: check each component pair. *)
Fixpoint functions_similar_b (pts1 pts2 : list (Fin * Fin)) 
                              (tolerance : Fin) (b : Budget)
  : (bool * Budget) :=
  match pts1, pts2, b with
  | [], [], _ => (true, b)
  | [], _, _ => (false, b)
  | _, [], _ => (false, b)
  | _, _, fz => (false, fz)
  | (_, y1) :: rest1, (_, y2) :: rest2, fs b' =>
      match dist_fin_b y1 y2 b' with
      | (d, b1) =>
          match le_fin_b d tolerance b1 with
          | (true, b2) => functions_similar_b rest1 rest2 tolerance b2
          | (false, b2) => (false, b2)  (* found difference: stop early *)
          end
      end
  end.

(* Are two DiscreteFunctions similar within tolerance? *)
Definition discrete_similar_b (f1 f2 : DiscreteFunction) (tolerance : Fin)
                               (b : Budget)
  : (bool * Budget) :=
  functions_similar_b (sample_points f1) (sample_points f2) tolerance b.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition discrete_to_vector_ext := discrete_to_vector_b.
Definition vector_to_discrete_ext := vector_to_discrete_b.
Definition function_distance_ext := function_distance_b.
Definition derivative_shape_ext := derivative_shape_b.
Definition discrete_similar_ext := discrete_similar_b.

End Void_Calculus_Geometry_Bridge.

(******************************************************************************)
(* WHY THIS BRIDGE EXISTS                                                     *)
(*                                                                            *)
(* void_calculus.v stores functions as list (Fin * Fin) — pairs of (x, y).  *)
(* void_geometry.v stores vectors as list FinProb — pairs of (num, den).    *)
(* Structurally identical: both are list (Fin * Fin).                        *)
(* Semantically disconnected: calculus never calls geometry, geometry never   *)
(* calls calculus.                                                            *)
(*                                                                            *)
(* This module provides:                                                      *)
(* - discrete_to_vector_b: function values as geometric vector               *)
(* - vector_to_discrete_b: geometric vector as function samples              *)
(* - function_distance_b: how far apart are two functions?                   *)
(* - derivative_shape_b: derivative as geometric shape                       *)
(* - discrete_similar_b: early-exit similarity check                         *)
(*                                                                            *)
(* One tick per sample point. Scale parameter lets caller choose              *)
(* the denominator for FinProb conversion. No new logic — composition        *)
(* of existing operations from both modules.                                  *)
(******************************************************************************)