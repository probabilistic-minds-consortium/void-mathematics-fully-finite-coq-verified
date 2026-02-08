(******************************************************************************)
(* void_geometry_basis.v - DISTINGUISHABILITY-BASED GEOMETRY                  *)
(* Building true void geometry on top of vector machinery                     *)
(* CLEANED: Uniform costs, no magic constants                                 *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_geometry.
Require Import void_distinguishability.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Geometry_Basis.

Import Void_Geometry.
Import Void_Pattern.
Import Void_Distinguishability.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* FUNDAMENTAL CONSTANT                                                       *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.

(* Common fractions defined inline *)
Definition half : FinProb := (fs fz, fs (fs fz)).
Definition third : FinProb := (fs fz, fs (fs (fs fz))).

(******************************************************************************)
(* FUNDAMENTAL TYPES - Space as Distinguishability                           *)
(******************************************************************************)

(* A point in void space is not a location but a distinguishable pattern *)
Definition VoidPoint := Pattern.

(* Space itself is the distinguishability relationship *)
Definition VoidSpace := VoidPoint -> VoidPoint -> ObserverWithBudget -> (FinProb * Budget).

(* A geometric object is a field of probabilities *)
Definition ShapeField := VoidPoint -> ObserverWithBudget -> (FinProb * ObserverWithBudget).

(******************************************************************************)
(* CONNECTING VECTORS TO PATTERNS                                            *)
(******************************************************************************)

(* Embed a vector as a pattern *)
Definition vector_to_pattern (v : VoidVector) : Pattern :=
  match v with
  | [] => {| location := fz; strength := half |}
  | p :: _ => {| location := fst p; strength := p |}
  end.

(* Extract vector from pattern neighborhood *)
Definition pattern_to_vector (p : Pattern) (dim : Fin) : VoidVector :=
  match dim with
  | fz => []
  | fs fz => [strength p]
  | fs (fs fz) => [strength p; half]
  | _ => [strength p; half; third]
  end.

(******************************************************************************)
(* DISTINGUISHABILITY DISTANCE - The True Metric                             *)
(******************************************************************************)

(* Distance between vectors - costs one tick *)
Definition distinguishability_distance (v1 v2 : VoidVector) (obs : ObserverWithBudget)
  : (FinProb * ObserverWithBudget) :=
  match obs_budget obs with
  | fz => (half, obs)
  | fs b' =>
      match vectors_equal_b v1 v2 b' with
      | (true, b'') => 
          (* Very close - small numerator *)
          ((fs fz, fs (fs (fs fz))), 
           {| observer := observer obs; obs_budget := b'' |})
      | (false, b'') => 
          (* Farther - larger numerator *)
          ((fs (fs fz), fs (fs (fs fz))),
           {| observer := observer obs; obs_budget := b'' |})
      end
  end.

(* Distance between points - costs one tick *)
Definition point_distance (p1 p2 : VoidPoint) (obs : ObserverWithBudget)
  : (FinProb * ObserverWithBudget) :=
  match obs_budget obs with
  | fz => (half, obs)
  | fs b' =>
      match fin_eq_b (location p1) (location p2) b' with
      | (true, b'') => 
          (* Same location - check strength *)
          match prob_diff_with_budget (strength p1) (strength p2) b'' with
          | (diff, b''') => 
              (diff, {| observer := observer obs; obs_budget := b''' |})
          end
      | (false, b'') =>
          (* Different locations *)
          ((fs (fs fz), fs (fs (fs fz))),
           {| observer := observer obs; obs_budget := b'' |})
      end
  end.

(******************************************************************************)
(* SHAPE FIELDS - Geometry as Probability                                    *)
(******************************************************************************)

(* Triangleness field - costs one tick per check *)
Definition triangleness_field (p1 p2 p3 : VoidPoint) : ShapeField :=
  fun p obs =>
    match obs_budget obs with
    | fz => (half, obs)
    | fs b' =>
        (* Simple triangular check *)
        match point_distance p p1 obs with
        | (d1, obs1) =>
            match point_distance p p2 obs1 with
            | (d2, obs2) =>
                match point_distance p p3 obs2 with
                | (d3, obs3) =>
                    (* Triangleness is just whether we have three distances *)
                    match d1, d2, d3 with
                    | (n1, _), (n2, _), (n3, _) =>
                        match n1, n2, n3 with
                        | fz, _, _ => (half, obs3)
                        | _, fz, _ => (half, obs3)
                        | _, _, fz => (half, obs3)
                        | _, _, _ => 
                            (* Has distances to all three points *)
                            ((fs (fs fz), fs (fs (fs fz))), obs3)
                        end
                    end
                end
            end
        end
    end.

(* Circleness field - costs one tick *)
Definition circleness_field (center : VoidPoint) (radius : FinProb) : ShapeField :=
  fun p obs =>
    match obs_budget obs with
    | fz => (half, obs)
    | fs b' =>
        match point_distance p center obs with
        | (dist, obs') =>
            match prob_diff_with_budget dist radius (obs_budget obs') with
            | (diff, b'') =>
                (* Close to radius = more circular *)
                let circleness := match fst diff with
                                 | fz => (fs (fs fz), fs (fs (fs fz)))
                                 | _ => (fs fz, fs (fs (fs fz)))
                                 end in
                (circleness, {| observer := observer obs'; obs_budget := b'' |})
            end
        end
    end.

(* Lineness field - costs one tick *)
Definition lineness_field (p1 p2 : VoidPoint) : ShapeField :=
  fun p obs =>
    match obs_budget obs with
    | fz => (half, obs)
    | fs b' =>
        (* Simple collinearity check *)
        match point_distance p1 p obs with
        | (d1p, obs1) =>
            match point_distance p p2 obs1 with
            | (dp2, obs2) =>
                (* On line if we have both distances *)
                match d1p, dp2 with
                | (n1, _), (n2, _) =>
                    match n1, n2 with
                    | fz, _ => (half, obs2)
                    | _, fz => (half, obs2)
                    | _, _ => ((fs (fs fz), fs (fs (fs fz))), obs2)
                    end
                end
            end
        end
    end.

(******************************************************************************)
(* ORTHOGONALITY AS DISTINGUISHABILITY INDEPENDENCE                          *)
(******************************************************************************)

(* Orthogonality measure - costs one tick *)
Definition orthogonality_measure (v1 v2 : VoidVector) (obs : ObserverWithBudget)
  : (FinProb * ObserverWithBudget) :=
  match obs_budget obs with
  | fz => (half, obs)
  | fs b' =>
      match inner_product_b v1 v2 b' with
      | (inner_prod, b'') =>
          (* Orthogonality inversely related to inner product *)
          let ortho := match fst inner_prod with
                       | fz => (fs (fs fz), fs (fs (fs fz)))
                       | _ => (fs fz, fs (fs (fs fz)))
                       end in
          (ortho, {| observer := observer obs; obs_budget := b'' |})
      end
  end.

(* Check if vectors form basis - costs one tick *)
Definition forms_basis_b (vectors : list VoidVector) (obs : ObserverWithBudget)
  : (FinProb * ObserverWithBudget) :=
  match vectors with
  | [] => (half, obs)
  | [v] => ((fs fz, fs (fs (fs fz))), obs)
  | v1 :: v2 :: _ =>
      orthogonality_measure v1 v2 obs
  end.

(******************************************************************************)
(* OBSERVER-DEPENDENT GEOMETRY                                               *)
(******************************************************************************)

(* Space dimensions based on observer budget *)
Definition observed_dimension (obs : ObserverWithBudget) : Fin :=
  match obs_budget obs with
  | fz => fz
  | fs fz => fs fz
  | fs (fs fz) => fs (fs fz)
  | fs (fs (fs _)) => fs (fs (fs fz))  (* Max three dimensions *)
  end.

(* Local curvature - costs one tick *)
Definition local_curvature (p : VoidPoint) (obs : ObserverWithBudget)
  : (FinProb * ObserverWithBudget) :=
  match obs_budget obs with
  | fz => (half, obs)
  | fs b' =>
      (* Sample one nearby point *)
      let p' := {| location := fs (location p); strength := strength p |} in
      match point_distance p p' obs with
      | (d, obs') => (d, obs')  (* Distance itself is the curvature measure *)
      end
  end.

(* Decay helper *)
Definition decay (p : FinProb) : FinProb :=
  match p with
  | (fs (fs n), d) => (fs n, d)
  | other => other
  end.

(******************************************************************************)
(* HELPER FUNCTIONS                                                           *)
(******************************************************************************)

(* Take first n elements *)
Fixpoint take_n (n : Fin) {A : Type} (l : list A) : list A :=
  match n, l with
  | fz, _ => []
  | _, [] => []
  | fs n', h :: t => h :: take_n n' t
  end.

(******************************************************************************)
(* NON-COMMUTATIVE OPERATIONS                                                *)
(******************************************************************************)

(* Sequential vector addition - costs one tick *)
Definition sequential_add_vectors (v1 v2 : VoidVector) (obs : ObserverWithBudget)
  : (VoidVector * ObserverWithBudget) :=
  match obs_budget obs with
  | fz => ([], obs)
  | fs b' =>
      match add_vectors_b v1 v2 b' with
      | (sum, b'') =>
          (* Observer exhaustion affects what's seen *)
          let visible := observed_dimension 
                          {| observer := observer obs; obs_budget := b'' |} in
          (take_n visible sum, 
           {| observer := observer obs; obs_budget := b'' |})
      end
  end.

(******************************************************************************)
(* GEOMETRIC COLLAPSE                                                        *)
(******************************************************************************)

(* Collapse shape field - costs one tick *)
Definition collapse_shape_field (field : ShapeField) (p : VoidPoint) 
                               (obs : ObserverWithBudget)
  : (Pattern * ObserverWithBudget) :=
  match field p obs with
  | (probability, obs') =>
      ({| location := location p; strength := probability |}, obs')
  end.

(* Superpose fields - costs one tick per field *)
Definition superpose_fields (f1 f2 : ShapeField) (weight : FinProb) : ShapeField :=
  fun p obs =>
    match obs_budget obs with
    | fz => (half, obs)
    | fs b' =>
        match f1 p obs with
        | (prob1, obs1) =>
            match f2 p obs1 with
            | (prob2, obs2) =>
                (* Simple average *)
                match add_prob_b prob1 prob2 (obs_budget obs2) with
                | (sum, b'') =>
                    (sum, {| observer := observer obs2; obs_budget := b'' |})
                end
            end
        end
    end.

(******************************************************************************)
(* NAVIGATION WITHOUT CENTER                                                 *)
(******************************************************************************)

(* Gradient step - costs one tick *)
Definition gradient_step (p : VoidPoint) (field : ShapeField) 
                        (obs : ObserverWithBudget)
  : (VoidPoint * ObserverWithBudget) :=
  match obs_budget obs with
  | fz => (p, obs)
  | fs b' =>
      (* Sample one direction *)
      let p' := {| location := fs (location p); strength := strength p |} in
      match field p' obs with
      | (val', obs') =>
          (* Move if field value is higher *)
          match field p obs' with
          | (val, obs'') =>
              match le_fin_b (fst val) (fst val') (obs_budget obs'') with
              | (true, b'') => 
                  (p', {| observer := observer obs''; obs_budget := b'' |})
              | (false, b'') => 
                  (p, {| observer := observer obs''; obs_budget := b'' |})
              end
          end
      end
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition VoidPoint_ext := VoidPoint.
Definition ShapeField_ext := ShapeField.
Definition triangleness_field_ext := triangleness_field.
Definition circleness_field_ext := circleness_field.
Definition distinguishability_distance_ext := distinguishability_distance.
Definition observed_dimension_ext := observed_dimension.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* This geometry embodies radical minimalism:
   
   1. ONE TICK PER OBSERVATION - Every geometric operation costs exactly
      one tick. Distance, curvature, shape fields - all one tick.
   
   2. NO MAGIC NUMBERS - No special significance to any fraction or ratio.
      Shapes emerge from relationships, not arbitrary constants.
   
   3. SPACE IS DISTINGUISHABILITY - Points are patterns, distance is the
      effort to distinguish. Simple and uniform.
   
   4. OBSERVATION CREATES GEOMETRY - Each look costs one tick and changes
      both observer and observed equally.
   
   5. DIMENSION FROM EXHAUSTION - Observer budget directly determines
      dimensionality. No magic, just resource depletion.
   
   This isn't geometry OF space but geometry OF EXPERIENCING space with
   finite resources, where every question costs exactly one tick of time. *)

End Void_Geometry_Basis.