(******************************************************************************)
(* void_sensory_transduction.v - FINITE SENSORY INTERFACE                    *)
(* Converting between finite representations - no infinity crosses this boundary *)
(*                                                                            *)
(* The external world must finitize itself before speaking to us.            *)
(* We only convert between Fin representations at different resolutions.     *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.

Module Void_Sensory_Transduction.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(*                                                                            *)
(* We do NOT accept nat. Ever. The infinite world is not our problem.        *)
(*                                                                            *)
(* External systems (Python, hardware) must convert their data to Fin        *)
(* BEFORE calling us. We provide the specification of what Fin we expect,    *)
(* and they must comply. If they send garbage, we saturate or reject.        *)
(*                                                                            *)
(* This module handles:                                                       *)
(* - Resolution conversion (rescaling Fin to different denominators)         *)
(* - Raw Fin lists → Pattern lists                                           *)
(* - Pattern → class decision (as Fin index)                                 *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* SECTION 1: RESOLUTION CONVERSION - Rescaling Fin values                   *)
(******************************************************************************)

(* 
   Rescale a Fin value from one resolution to another.
   
   Given value v at resolution r1, compute equivalent at resolution r2.
   This is finite division: (v * r2) / r1
   
   All values remain Fin. No infinity.
*)
Definition rescale_b (value : Fin) (from_res to_res : Fin) (b : Budget) 
  : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      match mult_fin value to_res b' with
      | (scaled, b1) =>
          match from_res with
          | fz => (scaled, b1)  (* Avoid division by zero - return scaled *)
          | _ =>
              match div_fin scaled from_res b1 with
              | (quotient, _, b2) => (quotient, b2)
              end
          end
      end
  end.

(*
   Clamp a Fin value to a maximum.
   If value > max, return max. Otherwise return value.
*)
Definition clamp_to_max_b (value max_val : Fin) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      match le_fin_b value max_val b' with
      | (true, b1) => (value, b1)
      | (false, b1) => (max_val, b1)
      end
  end.

(******************************************************************************)
(* SECTION 2: RAW FIN TO STRENGTH - Converting sensor values to probabilities *)
(******************************************************************************)

(*
   Convert a raw Fin sensor value to a FinProb strength.
   
   Input: value in range [0, max_value]
   Output: probability in open interval (0, 1)
   
   Transform: (value + 1) / (max_value + 2)
   - When value = 0: strength = 1 / (max + 2) ≈ near zero
   - When value = max: strength = (max + 1) / (max + 2) ≈ near one
   
   We never hit 0 or 1 exactly.
*)
Definition raw_to_strength_b (value max_value : Fin) (b : Budget) 
  : (FinProb * Budget) :=
  match b with
  | fz => ((fs fz, fs (fs fz)), fz)  (* Default: 1/2 *)
  | fs b' =>
      match safe_succ_b value b' with
      | (numerator, b1) =>
          match safe_succ_b max_value b1 with
          | (max_plus_one, b2) =>
              match safe_succ_b max_plus_one b2 with
              | (denominator, b3) =>
                  ((numerator, denominator), b3)
              end
          end
      end
  end.

(*
   Convert a raw Fin value at a given location to a Pattern.
*)
Definition raw_to_pattern_b (value max_value : Fin) (loc : Fin) (b : Budget)
  : (Pattern * Budget) :=
  match raw_to_strength_b value max_value b with
  | (str, b') =>
      ({| location := loc; strength := str |}, b')
  end.

(******************************************************************************)
(* SECTION 3: INPUT NORMALIZATION - Raw Fin list to Pattern list             *)
(******************************************************************************)

(*
   Process a list of raw sensor values into Patterns.
   Each value becomes a Pattern at its index position.
   
   The caller provides:
   - raw_values: list of Fin sensor readings
   - max_value: the maximum possible sensor value (for normalization)
   - budget: computational resources
   
   Returns patterns with locations 0, 1, 2, ... matching input indices.
*)
Fixpoint normalize_input_helper (raw_values : list Fin) (max_value : Fin)
                                 (current_loc : Fin) (fuel : Fin) (b : Budget)
  : (list Pattern * Budget) :=
  match fuel with
  | fz => ([], b)  (* Fuel exhausted - stop *)
  | fs fuel' =>
      match raw_values with
      | [] => ([], b)
      | value :: rest =>
          match b with
          | fz => ([], fz)  (* Budget exhausted - return partial *)
          | fs b' =>
              match raw_to_pattern_b value max_value current_loc b' with
              | (pattern, b1) =>
                  match safe_succ_b current_loc b1 with
                  | (next_loc, b2) =>
                      match normalize_input_helper rest max_value next_loc fuel' b2 with
                      | (rest_patterns, b3) =>
                          (pattern :: rest_patterns, b3)
                      end
                  end
              end
          end
      end
  end.

(*
   Main entry point for input normalization.
   
   max_value: the maximum sensor reading (e.g., fs^255 fz for 8-bit)
   fuel: limits how many values we process (prevents unbounded recursion)
*)
Definition normalize_input_b (raw_values : list Fin) (max_value : Fin) 
                             (fuel : Fin) (b : Budget)
  : (list Pattern * Budget) :=
  normalize_input_helper raw_values max_value fz fuel b.

(******************************************************************************)
(* SECTION 4: OUTPUT DECODING - Pattern to class decision                    *)
(******************************************************************************)

(*
   Given output Pattern and number of classes, determine which class.
   
   Strategy: The pattern's location indicates which class region it's in.
   We divide the location space into num_classes regions.
   
   class_index = location / (location_range / num_classes)
   
   Simpler: class_index = (location * num_classes) / max_location
*)
Definition decode_to_class_b (p : Pattern) (num_classes max_location : Fin) (b : Budget)
  : (Fin * FinProb * Budget) :=
  match b with
  | fz => (fz, (fs fz, fs (fs fz)), fz)  (* No budget: class 0, half confidence *)
  | fs b' =>
      match num_classes with
      | fz => (fz, strength p, b')  (* No classes defined *)
      | _ =>
          match max_location with
          | fz => (fz, strength p, b')  (* No location range *)
          | _ =>
              match mult_fin (location p) num_classes b' with
              | (scaled, b1) =>
                  match div_fin scaled max_location b1 with
                  | (class_idx, _, b2) =>
                      (* Clamp to valid class range *)
                      match sub_fin num_classes (fs fz) b2 with
                      | (max_class, b3) =>
                          match clamp_to_max_b class_idx max_class b3 with
                          | (final_class, b4) =>
                              (final_class, strength p, b4)
                          end
                      end
                  end
              end
          end
      end
  end.

(*
   Alternative decoder: find which class center is closest to pattern location.
   
   Classes are assumed to have centers at evenly spaced locations:
   class_i center = (i * max_location) / num_classes + offset
*)
Fixpoint find_closest_class_b (target : Fin) (class_centers : list Fin)
                               (current_idx : Fin) (best_idx : Fin)
                               (best_dist : Fin) (fuel : Fin) (b : Budget)
  : (Fin * Budget) :=
  match fuel with
  | fz => (best_idx, b)
  | fs fuel' =>
      match class_centers with
      | [] => (best_idx, b)
      | center :: rest =>
          match b with
          | fz => (best_idx, fz)
          | fs b' =>
              match dist_fin_b target center b' with
              | (dist, b1) =>
                  match le_fin_b dist best_dist b1 with
                  | (true, b2) =>
                      (* Found closer class *)
                      match safe_succ_b current_idx b2 with
                      | (next_idx, b3) =>
                          find_closest_class_b target rest next_idx 
                                               current_idx dist fuel' b3
                      end
                  | (false, b2) =>
                      (* Keep current best *)
                      match safe_succ_b current_idx b2 with
                      | (next_idx, b3) =>
                          find_closest_class_b target rest next_idx 
                                               best_idx best_dist fuel' b3
                      end
                  end
              end
          end
      end
  end.

(*
   Generate class centers given num_classes and max_location.
   Centers are at: max_location * (2*i + 1) / (2 * num_classes)
   Simplified: we just use i * (max_location / num_classes)
*)
Fixpoint generate_class_centers (num_classes max_location : Fin) 
                                 (current_class : Fin) (fuel : Fin) (b : Budget)
  : (list Fin * Budget) :=
  match fuel with
  | fz => ([], b)
  | fs fuel' =>
      match le_fin_b current_class num_classes b with
      | (false, b1) => ([], b1)  (* Generated all classes *)
      | (true, b1) =>
          match b1 with
          | fz => ([], fz)
          | fs b2 =>
              (* center = current_class * max_location / num_classes *)
              match mult_fin current_class max_location b2 with
              | (scaled, b3) =>
                  match div_fin scaled num_classes b3 with
                  | (center, _, b4) =>
                      match safe_succ_b current_class b4 with
                      | (next_class, b5) =>
                          match generate_class_centers num_classes max_location 
                                                       next_class fuel' b5 with
                          | (rest_centers, b6) =>
                              (center :: rest_centers, b6)
                          end
                      end
                  end
              end
          end
      end
  end.

(*
   Full closest-class decoder.
*)
Definition decode_closest_class_b (p : Pattern) (num_classes max_location : Fin)
                                  (fuel : Fin) (b : Budget)
  : (Fin * FinProb * Budget) :=
  match b with
  | fz => (fz, (fs fz, fs (fs fz)), fz)
  | fs b' =>
      match generate_class_centers num_classes max_location fz fuel b' with
      | (centers, b1) =>
          match centers with
          | [] => (fz, strength p, b1)
          | first_center :: _ =>
              match dist_fin_b (location p) first_center b1 with
              | (initial_dist, b2) =>
                  match find_closest_class_b (location p) centers 
                                             fz fz initial_dist fuel b2 with
                  | (class_idx, b3) => (class_idx, strength p, b3)
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* SECTION 5: FILTERING - Sparse input processing                            *)
(******************************************************************************)

(*
   Activity threshold - patterns below this are considered inactive.
*)
Definition activity_threshold : FinProb := (fs fz, fs (fs (fs (fs fz)))).  (* 1/4 *)

(*
   Check if a pattern is active (strength above threshold).
*)
Definition is_active_b (p : Pattern) (threshold : FinProb) (b : Budget)
  : (bool * Budget) :=
  prob_le_b threshold (strength p) b.

(*
   Filter to only active patterns - saves downstream computation.
*)
Fixpoint filter_active_helper (patterns : list Pattern) (threshold : FinProb)
                               (fuel : Fin) (b : Budget)
  : (list Pattern * Budget) :=
  match fuel with
  | fz => ([], b)
  | fs fuel' =>
      match patterns with
      | [] => ([], b)
      | p :: rest =>
          match b with
          | fz => ([], fz)
          | fs b' =>
              match is_active_b p threshold b' with
              | (true, b1) =>
                  match filter_active_helper rest threshold fuel' b1 with
                  | (rest_active, b2) => (p :: rest_active, b2)
                  end
              | (false, b1) =>
                  filter_active_helper rest threshold fuel' b1
              end
          end
      end
  end.

Definition filter_active_b (patterns : list Pattern) (fuel : Fin) (b : Budget)
  : (list Pattern * Budget) :=
  filter_active_helper patterns activity_threshold fuel b.

(******************************************************************************)
(* SECTION 6: BATCH PROCESSING                                               *)
(******************************************************************************)

(*
   Process multiple input samples.
*)
Fixpoint normalize_batch_helper (samples : list (list Fin)) (max_value : Fin)
                                 (fuel : Fin) (b : Budget)
  : (list (list Pattern) * Budget) :=
  match fuel with
  | fz => ([], b)
  | fs fuel' =>
      match samples with
      | [] => ([], b)
      | sample :: rest =>
          match b with
          | fz => ([], fz)
          | fs b' =>
              match normalize_input_b sample max_value fuel' b' with
              | (patterns, b1) =>
                  match normalize_batch_helper rest max_value fuel' b1 with
                  | (rest_normalized, b2) =>
                      (patterns :: rest_normalized, b2)
                  end
              end
          end
      end
  end.

Definition normalize_batch_b (samples : list (list Fin)) (max_value : Fin)
                             (fuel : Fin) (b : Budget)
  : (list (list Pattern) * Budget) :=
  normalize_batch_helper samples max_value fuel b.

(*
   Decode multiple output patterns.
*)
Fixpoint decode_batch_helper (outputs : list Pattern) (num_classes max_location : Fin)
                              (fuel : Fin) (b : Budget)
  : (list (Fin * FinProb) * Budget) :=
  match fuel with
  | fz => ([], b)
  | fs fuel' =>
      match outputs with
      | [] => ([], b)
      | p :: rest =>
          match b with
          | fz => ([], fz)
          | fs b' =>
              match decode_to_class_b p num_classes max_location b' with
              | (class_idx, confidence, b1) =>
                  match decode_batch_helper rest num_classes max_location fuel' b1 with
                  | (rest_decoded, b2) =>
                      ((class_idx, confidence) :: rest_decoded, b2)
                  end
              end
          end
      end
  end.

Definition decode_batch_b (outputs : list Pattern) (num_classes max_location : Fin)
                          (fuel : Fin) (b : Budget)
  : (list (Fin * FinProb) * Budget) :=
  decode_batch_helper outputs num_classes max_location fuel b.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition rescale_b_ext := rescale_b.
Definition raw_to_strength_b_ext := raw_to_strength_b.
Definition raw_to_pattern_b_ext := raw_to_pattern_b.
Definition normalize_input_b_ext := normalize_input_b.
Definition decode_to_class_b_ext := decode_to_class_b.
Definition decode_closest_class_b_ext := decode_closest_class_b.
Definition filter_active_b_ext := filter_active_b.
Definition normalize_batch_b_ext := normalize_batch_b.
Definition decode_batch_b_ext := decode_batch_b.

(******************************************************************************)
(* PHILOSOPHICAL CODA                                                         *)
(*                                                                            *)
(* This module is the sensory membrane of void mathematics.                  *)
(*                                                                            *)
(* We do NOT convert from nat. The infinite world must finitize itself       *)
(* before speaking to us. External systems (Python, hardware) bear the       *)
(* burden of bounding their data. We specify what Fin we accept; they comply.*)
(*                                                                            *)
(* What we DO handle:                                                         *)
(*                                                                            *)
(* 1. RESOLUTION CONVERSION - Rescaling between different Fin granularities  *)
(*    A 256-level sensor reading becomes a 16-level internal value.          *)
(*                                                                            *)
(* 2. STRENGTH MAPPING - Raw Fin → FinProb via (v+1)/(max+2)                 *)
(*    Always lands in open interval (0,1). No certainty from raw data.       *)
(*                                                                            *)
(* 3. SPATIAL ENCODING - Values become Patterns with location = index        *)
(*    The topology of input is preserved in pattern locations.               *)
(*                                                                            *)
(* 4. CLASS DECODING - Pattern location → class index                        *)
(*    The network "points" somewhere; we read which class region.            *)
(*                                                                            *)
(* 5. SPARSE FILTERING - Skip inactive patterns to save budget               *)
(*    Attention begins at perception: don't waste resources on zeros.        *)
(*                                                                            *)
(* All operations consume budget. All use fuel for termination.              *)
(* The network sees only what it can afford to perceive.                     *)
(******************************************************************************)

End Void_Sensory_Transduction.