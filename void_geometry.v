(******************************************************************************)
(* void_geometry.v - BUDGET-AWARE FINITE GEOMETRY                            *)
(* Geometry for finite observers - no escape to infinity!                     *)
(* Creating vectors, measuring dimensions, comparing - all cost budget        *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.

Module Void_Geometry.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* SYSTEM CONSTANTS - Given by the void                                      *)
(******************************************************************************)

Parameter vector_create_cost : Fin.
Parameter component_cost : Fin.
Parameter comparison_cost : Fin.

Axiom create_cost_spec : vector_create_cost = fs fz.
Axiom component_cost_spec : component_cost = fs fz.
Axiom comparison_cost_spec : comparison_cost = fs fz.

(******************************************************************************)
(* BASIC TYPES WITH BUDGET AWARENESS                                         *)
(******************************************************************************)

(* A void vector is a list of probability values *)
Definition VoidVector := list FinProb.

(* Vector with budget tracking *)
Record BudgetedVector := {
  vector : VoidVector;
  vec_budget : Budget
}.

(******************************************************************************)
(* VECTOR CREATION WITH BUDGET                                               *)
(******************************************************************************)

(* The empty vector - costs nothing but we track it *)
Definition empty_vector_b (b : Budget) : (BudgetedVector * Budget) :=
  ({| vector := []; vec_budget := b |}, b).

(* A singleton vector - costs budget to create *)
Definition singleton_vector_b (p : FinProb) (b : Budget) : (BudgetedVector * Budget) :=
  match b with
  | fz => ({| vector := []; vec_budget := fz |}, fz)  (* No budget - empty *)
  | fs b' =>
      match sub_fin b' vector_create_cost b' with
      | (_, b'') =>
          ({| vector := [p]; vec_budget := b'' |}, b'')
      end
  end.

(******************************************************************************)
(* VECTOR VALIDITY - A PHILOSOPHICAL PROPERTY                                *)
(******************************************************************************)

(* A valid vector has all components avoiding void boundaries *)
Definition valid_vector (v : VoidVector) : Prop :=
  forall p, In p v -> avoids_zero p /\ 
                      match p with
                      | (n, d) => n <> d  (* avoids one *)
                      end.

(******************************************************************************)
(* MEASURING WITH BUDGET                                                     *)
(******************************************************************************)

(* Measuring dimension costs budget per component *)
Fixpoint dimension_with_budget (v : VoidVector) (b : Budget) : (Fin * Budget) :=
  match v, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: v', fs b' =>
      match dimension_with_budget v' b' with
      | (count, b'') => (fs count, b'')
      end
  end.

(******************************************************************************)
(* VECTOR GENERATION WITHOUT NAT - STAYING FINITE                            *)
(******************************************************************************)

(* Generate list of given length - costs budget per element *)
Fixpoint repeat_with_budget (p : FinProb) (n : Fin) (b : Budget) 
  : (VoidVector * Budget) :=
  match n, b with
  | fz, _ => ([], b)
  | _, fz => ([], fz)
  | fs n', fs b' =>
      match repeat_with_budget p n' b' with
      | (rest, b'') => (p :: rest, b'')
      end
  end.

(* The uncertain vector - maximum uncertainty in all components *)
Definition uncertain_vector_b (dim : Fin) (b : Budget) : (BudgetedVector * Budget) :=
  match mult_fin dim component_cost b with
  | (total_cost, b1) =>
      match le_fin_b total_cost b1 b1 with
      | (false, b2) => 
          (* Can't afford full vector *)
          ({| vector := []; vec_budget := b2 |}, b2)
      | (true, b2) =>
          match sub_fin b2 total_cost b2 with
          | (_, b3) =>
              match repeat_with_budget half dim b3 with
              | (vec, b4) =>
                  ({| vector := vec; vec_budget := b4 |}, b4)
              end
          end
      end
  end.

(* Generate indices within Fin - no nat needed! *)
Fixpoint generate_indices_b (n : Fin) (current : Fin) (b : Budget) 
  : (list Fin * Budget) :=
  match n, b with
  | fz, _ => ([], b)
  | _, fz => ([], fz)
  | fs n', fs b' =>
      match generate_indices_b n' (fs current) b' with
      | (rest, b'') => (current :: rest, b'')
      end
  end.

(* Near-basis vector - leans toward one component *)
Definition near_basis_vector_b (dim : Fin) (component : Fin) (b : Budget) 
  : (BudgetedVector * Budget) :=
  let high := (fs (fs (fs fz)), fs (fs (fs (fs fz)))) in  (* 3/4 *)
  let low := (fs fz, fs (fs (fs (fs fz)))) in            (* 1/4 *)
  
  match mult_fin dim component_cost b with
  | (total_cost, b1) =>
      match le_fin_b total_cost b1 b1 with
      | (false, b2) => 
          ({| vector := []; vec_budget := b2 |}, b2)
      | (true, b2) =>
          match sub_fin b2 total_cost b2 with
          | (_, b3) =>
              match generate_indices_b dim fz b3 with
              | (indices, b4) =>
                  (* Map over indices with budget *)
                  let build_component := fold_left (fun acc idx =>
                    match acc with
                    | (vec, b_acc) =>
                        match b_acc with
                        | fz => (vec, fz)
                        | fs b' =>
                            match fin_eq_b idx component b' with
                            | (true, b'') => (vec ++ [high], b'')
                            | (false, b'') => (vec ++ [low], b'')
                            end
                        end
                    end
                  ) indices ([], b4) in
                  match build_component with
                  | (vec, b5) =>
                      ({| vector := vec; vec_budget := b5 |}, b5)
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* VECTOR OPERATIONS WITH BUDGET                                             *)
(******************************************************************************)

(* Vector equality check - costs budget *)
Fixpoint vectors_equal_b (v1 v2 : VoidVector) (b : Budget) 
  : (bool * Budget) :=
  match v1, v2, b with
  | [], [], _ => (true, b)
  | [], _ :: _, _ => (false, b)
  | _ :: _, [], _ => (false, b)
  | _, _, fz => (true, fz)  (* No budget - assume equal *)
  | p1 :: v1', p2 :: v2', fs b' =>
      match prob_eq_b p1 p2 b' with
      | (true, b'') => vectors_equal_b v1' v2' b''
      | (false, b'') => (false, b'')
      end
  end.

(* Add vectors componentwise - costs budget *)
Fixpoint add_vectors_b (v1 v2 : VoidVector) (b : Budget) 
  : (VoidVector * Budget) :=
  match v1, v2, b with
  | [], [], _ => ([], b)
  | [], _, _ => (v2, b)  (* Different dimensions *)
  | _, [], _ => (v1, b)
  | _, _, fz => ([], fz)  (* No budget *)
  | p1 :: v1', p2 :: v2', _ =>
      match add_prob_b p1 p2 b with
      | (sum, b1) =>
          match add_vectors_b v1' v2' b1 with
          | (rest, b2) => (sum :: rest, b2)
          end
      end
  end.

(* Multiply probabilities with budget *)
Definition mult_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin n1 n2 b with
  | (new_n, b1) =>
      match mult_fin d1 d2 b1 with
      | (new_d, b2) => ((new_n, new_d), b2)
      end
  end.

(* Inner product - very expensive operation *)
Fixpoint inner_product_b (v1 v2 : VoidVector) (b : Budget) 
  : (FinProb * Budget) :=
  match v1, v2, b with
  | [], [], _ => ((fz, fs fz), b)  (* Zero (impossible but needed) *)
  | [], _, _ => ((fs fz, fs (fs (fs (fs fz)))), b)  (* 1/4 default *)
  | _, [], _ => ((fs fz, fs (fs (fs (fs fz)))), b)
  | _, _, fz => ((fs fz, fs (fs (fs (fs fz)))), fz)
  | p1 :: v1', p2 :: v2', _ =>
      (* Multiply components *)
      match mult_prob_b p1 p2 b with
      | (prod, b1) =>
          match inner_product_b v1' v2' b1 with
          | (rest_prod, b2) =>
              add_prob_b prod rest_prod b2
          end
      end
  end.

(* Distance between vectors - expensive *)
Definition vector_distance_b (v1 v2 : VoidVector) (b : Budget) 
  : (Fin * Budget) :=
  match v1, v2 with
  | [], [] => (fz, b)
  | _, _ =>
      fold_left (fun acc pair =>
        match acc with
        | (dist_acc, b_acc) =>
            match pair with
            | (p1, p2) =>
                match b_acc with
                | fz => (dist_acc, fz)
                | _ =>
                    match dist_fin_b (fst p1) (fst p2) b_acc with
                    | (comp_dist, b') =>
                        match add_fin dist_acc comp_dist b' with
                        | (new_dist, b'') => (new_dist, b'')
                        end
                    end
                end
            end
        end
      ) (combine v1 v2) (fz, b)
  end.

(******************************************************************************)
(* PHILOSOPHICAL OPERATIONS                                                   *)
(******************************************************************************)

(* The "void projection" - collapse toward uncertainty *)
Definition void_projection_b (bv : BudgetedVector) : BudgetedVector :=
  match vec_budget bv with
  | fz => bv  (* No budget - frozen *)
  | fs b' =>
      let project_component := fun p =>
        match p with
        | (n, d) =>
            (* Move numerator toward half of denominator *)
            match div_fin d (fs (fs fz)) b' with
            | (half_d, _, _) => (half_d, d)
            end
        end in
      {| vector := map project_component (vector bv);
         vec_budget := b' |}
  end.

(* Boolean and helper *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with true => b2 | false => false end.

(* Check if vector is near void (maximum uncertainty) *)
Definition near_void_b (bv : BudgetedVector) : (bool * Budget) :=
  fold_left (fun acc p =>
    match acc with
    | (all_half, b) =>
        match b with
        | fz => (all_half, fz)
        | fs b' =>
            match prob_eq_b p half b' with
            | (is_half, b'') => (andb all_half is_half, b'')
            end
        end
    end
  ) (vector bv) (true, vec_budget bv).

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition VoidVector_ext := VoidVector.
Definition BudgetedVector_ext := BudgetedVector.
Definition dimension_with_budget_ext := dimension_with_budget.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Void geometry reveals the true nature of finite space:
   
   1. NO ESCAPE TO INFINITY - We never use nat. Everything stays within
      Fin. There is no backdoor to the infinite.
   
   2. CREATION COSTS - Vectors don't exist for free. Every component
      costs budget to create. The larger the space, the more expensive
      to populate it.
   
   3. BASIS WITHOUT EXTREMES - Our "basis" vectors can only lean toward
      components (3/4) while maintaining uncertainty (1/4). True basis
      vectors with 0s and 1s are impossible.
   
   4. MEASUREMENT DEPLETES - Even counting dimensions costs. You can't
      know the size of a space without paying to measure it.
   
   5. THE VOID PROJECTION - All vectors tend toward maximum uncertainty
      (all components = 1/2) as operations exhaust budgets.
   
   This is geometry where space itself costs resources to explore and
   populate. The classical infinite-dimensional vector spaces are revealed
   as budget-unlimited fantasies. Real geometry happens in finite spaces
   where every dimension costs, every measurement depletes, and all
   vectors eventually collapse toward the uncertain center. *)

End Void_Geometry.