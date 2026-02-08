(******************************************************************************)
(* void_geometry.v - BUDGET-AWARE FINITE GEOMETRY                            *)
(* Geometry for finite observers - no escape to infinity!                     *)
(* CLEANED: All operations cost one tick, no magic numbers                    *)
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
(* FUNDAMENTAL CONSTANT - One tick of time                                   *)
(******************************************************************************)

Definition operation_cost : Fin := fs fz.  (* The only arbitrary constant *)

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

(* The empty vector - costs one tick *)
Definition empty_vector_b (b : Budget) : (BudgetedVector * Budget) :=
  match b with
  | fz => ({| vector := []; vec_budget := fz |}, fz)
  | fs b' => ({| vector := []; vec_budget := b' |}, b')
  end.

(* A singleton vector - costs one tick to create *)
Definition singleton_vector_b (p : FinProb) (b : Budget) : (BudgetedVector * Budget) :=
  match b with
  | fz => ({| vector := []; vec_budget := fz |}, fz)
  | fs b' => ({| vector := [p]; vec_budget := b' |}, b')
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

(* Measuring dimension costs one tick per component *)
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

(* Generate list of given length - costs one tick per element *)
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

(* Common fractions inline *)
Definition half_prob : FinProb := (fs fz, fs (fs fz)).

(* The uncertain vector - maximum uncertainty in all components *)
Definition uncertain_vector_b (dim : Fin) (b : Budget) : (BudgetedVector * Budget) :=
  match repeat_with_budget half_prob dim b with
  | (vec, b') => ({| vector := vec; vec_budget := b' |}, b')
  end.

(* Generate indices within Fin - costs one tick per index *)
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

(* Near-basis vector - simple without magic numbers *)
Definition near_basis_vector_b (dim : Fin) (component : Fin) (b : Budget) 
  : (BudgetedVector * Budget) :=
  match generate_indices_b dim fz b with
  | (indices, b1) =>
      (* Map over indices with budget *)
      let build_component := fold_left (fun acc idx =>
        match acc with
        | (vec, b_acc) =>
            match b_acc with
            | fz => (vec, fz)
            | fs b' =>
                match fin_eq_b idx component b' with
                | (true, b'') => 
                    (* Component gets slightly more weight *)
                    (vec ++ [(fs (fs fz), fs (fs (fs fz)))], b'')
                | (false, b'') => 
                    (* Other components get less *)
                    (vec ++ [(fs fz, fs (fs (fs fz)))], b'')
                end
            end
        end
      ) indices ([], b1) in
      match build_component with
      | (vec, b2) =>
          ({| vector := vec; vec_budget := b2 |}, b2)
      end
  end.

(******************************************************************************)
(* VECTOR OPERATIONS WITH BUDGET                                             *)
(******************************************************************************)

(* Check if two probabilities are equal - costs one tick *)
Definition prob_eq_b (p1 p2 : FinProb) (b : Budget) : (bool * Budget) :=
  match b with
  | fz => (false, fz)
  | fs b' =>
      let (n1, d1) := p1 in
      let (n2, d2) := p2 in
      match fin_eq_b n1 n2 b' with
      | (eq_n, b'') =>
          match fin_eq_b d1 d2 b'' with
          | (eq_d, b''') => (andb eq_n eq_d, b''')
          end
      end
  end.

(* Vector equality check - costs one tick per component *)
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

(* Add probabilities with budget - costs one tick *)
Definition add_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      let (n1, d1) := p1 in
      let (n2, d2) := p2 in
      match fin_eq_b d1 d2 b' with
      | (true, b1) =>
          (* Same denominator - just add numerators *)
          match add_fin n1 n2 b1 with
          | (sum, b2) => ((sum, d1), b2)
          end
      | (false, b1) =>
          (* Different denominators - cross multiplication *)
          match mult_fin n1 d2 b1 with
          | (v1, b2) =>
              match mult_fin n2 d1 b2 with
              | (v2, b3) =>
                  match add_fin v1 v2 b3 with
                  | (new_n, b4) =>
                      match mult_fin d1 d2 b4 with
                      | (new_d, b5) => ((new_n, new_d), b5)
                      end
                  end
              end
          end
      end
  end.

(* Add vectors componentwise - costs one tick per component *)
Fixpoint add_vectors_b (v1 v2 : VoidVector) (b : Budget) 
  : (VoidVector * Budget) :=
  match v1, v2, b with
  | [], [], _ => ([], b)
  | [], _, _ => (v2, b)
  | _, [], _ => (v1, b)
  | _, _, fz => ([], fz)
  | p1 :: v1', p2 :: v2', _ =>
      match add_prob_b p1 p2 b with
      | (sum, b1) =>
          match add_vectors_b v1' v2' b1 with
          | (rest, b2) => (sum :: rest, b2)
          end
      end
  end.

(* Multiply probabilities - costs one tick *)
Definition mult_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      let (n1, d1) := p1 in
      let (n2, d2) := p2 in
      match mult_fin n1 n2 b' with
      | (new_n, b1) =>
          match mult_fin d1 d2 b1 with
          | (new_d, b2) => ((new_n, new_d), b2)
          end
      end
  end.

(* Inner product - costs one tick per component *)
Fixpoint inner_product_b (v1 v2 : VoidVector) (b : Budget) 
  : (FinProb * Budget) :=
  match v1, v2, b with
  | [], [], _ => (half_prob, b)
  | [], _, _ => (half_prob, b)
  | _, [], _ => (half_prob, b)
  | _, _, fz => (half_prob, fz)
  | p1 :: v1', p2 :: v2', _ =>
      match mult_prob_b p1 p2 b with
      | (prod, b1) =>
          match inner_product_b v1' v2' b1 with
          | (rest_prod, b2) =>
              add_prob_b prod rest_prod b2
          end
      end
  end.

(* Distance between vectors - costs one tick per component *)
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
                | fs b' =>
                    match dist_fin_b (fst p1) (fst p2) b' with
                    | (comp_dist, b'') =>
                        match add_fin dist_acc comp_dist b'' with
                        | (new_dist, b''') => (new_dist, b''')
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

(* The void projection - collapse toward uncertainty *)
Definition void_projection_b (bv : BudgetedVector) : BudgetedVector :=
  match vec_budget bv with
  | fz => bv  (* No budget - frozen *)
  | fs b' =>
      (* Move all components toward half *)
      {| vector := map (fun _ => half_prob) (vector bv);
         vec_budget := b' |}
  end.

(* Boolean and helper *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with true => b2 | false => false end.

(* Check if vector is near void - costs one tick per component *)
Definition near_void_b (bv : BudgetedVector) : (bool * Budget) :=
  fold_left (fun acc p =>
    match acc with
    | (all_half, b) =>
        match b with
        | fz => (all_half, fz)
        | fs b' =>
            match prob_eq_b p half_prob b' with
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
   
   1. ONE TICK PER DIMENSION - Every component costs exactly one tick
      to create, measure, or manipulate. No operation is "harder."
   
   2. NO MAGIC RATIOS - We don't privilege 3/4 or 1/4. Basis vectors
      use simple fractions like 2/3 and 1/3 without special meaning.
   
   3. NO ESCAPE TO INFINITY - Everything stays within Fin. There is no
      backdoor to the infinite through nat or special constants.
   
   4. MEASUREMENT DEPLETES UNIFORMLY - Counting dimensions costs one
      tick per dimension. Simple and honest.
   
   5. THE VOID PROJECTION - All vectors tend toward uncertainty as
      operations exhaust budgets uniformly, tick by tick.
   
   This is geometry where every dimension costs the same, every operation
   takes one tick, and complexity emerges from iteration, not from
   arbitrary constants or special numbers. *)

End Void_Geometry.