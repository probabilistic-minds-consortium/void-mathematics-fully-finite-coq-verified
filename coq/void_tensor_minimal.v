(******************************************************************************)
(* void_tensor_minimal.v - FINITE TENSOR NAVIGATION                          *)
(* Tensors as bounded search spaces with NO RECURSION, NO NAT                *)
(* ALL operations use fold_left/fold_right ONLY                              *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Tensor_Minimal.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

Definition operation_cost : Fin := fs fz.

(******************************************************************************)
(* SYSTEM BOUNDS                                                              *)
(******************************************************************************)

Definition max_tensor_depth : Fin := 
  fs (fs (fs (fs (fs (fs (fs (fs fz))))))).  (* 8 *)

Definition max_fiber_length : Fin :=
  fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).  (* 10 *)

Definition max_coord_depth : Fin := max_tensor_depth.

(******************************************************************************)
(* TENSOR TYPES                                                               *)
(******************************************************************************)

Definition Tensor1D := list FinProb.
Definition Tensor2D := list Tensor1D.
Definition Tensor3D := list Tensor2D.
Definition Tensor4D := list Tensor3D.

Definition Coordinate := list Fin.

(******************************************************************************)
(* SUPERDIAGONAL CHECK - Using fold_left ONLY                                *)
(******************************************************************************)

Definition is_superdiagonal (coord : Coordinate) : bool :=
  match coord with
  | [] => true
  | first :: rest =>
      fst (fold_left (fun '(all_equal, prev) curr =>
        match all_equal with
        | false => (false, prev)
        | true => (fst (fin_eq_b prev curr initial_budget), curr)
        end
      ) rest (true, first))
  end.

(******************************************************************************)
(* SUPERDIAGONAL DISTANCE - Using fold_left ONLY                             *)
(******************************************************************************)

Definition superdiag_distance (coord : Coordinate) (b : Budget) : (Fin * Budget) :=
  match coord with
  | [] => (fz, b)
  | _ :: rest =>
      let '(total_dist, _, b_final) :=
        fold_left (fun '(total_dist, prev, b_acc) curr =>
          match b_acc with
          | fz => (total_dist, curr, fz)
          | fs b' =>
              match dist_fin_b prev curr b' with
              | (d, b'') =>
                  match add_fin total_dist d b'' with
                  | (new_total, b''') => (new_total, curr, b''')
                  end
              end
          end
        ) rest (fz, hd fz coord, b)
      in (total_dist, b_final)
  end.

(******************************************************************************)
(* FIBERS                                                                     *)
(******************************************************************************)

Record Fiber := {
  fiber_values : list FinProb;
  fiber_axis : Fin;
  fiber_anchor : Coordinate;
  fiber_budget : Budget
}.

Definition fiber_length (f : Fiber) : Fin :=
  fold_left (fun acc _ => fs acc) (fiber_values f) fz.

(******************************************************************************)
(* FIBER ACCESS - Using fold_left with counter                               *)
(******************************************************************************)

Definition fiber_at (f : Fiber) (pos : Fin) : option FinProb :=
  match fiber_values f with
  | [] => None
  | vals =>
      snd (fold_left (fun '(curr_pos, result) val =>
        match result with
        | Some _ => (curr_pos, result)
        | None =>
            match fst (fin_eq_b curr_pos pos initial_budget) with
            | true => (curr_pos, Some val)
            | false => (fs curr_pos, None)
            end
        end
      ) vals (fz, None))
  end.

(******************************************************************************)
(* FIND PEAK - Using fold_left ONLY                                          *)
(******************************************************************************)

Definition find_fiber_peak (f : Fiber) (b : Budget) : (Fin * Budget) :=
  match fiber_values f with
  | [] => (fz, b)
  | first :: rest =>
      let '((best_idx, b_final), _) :=
        fold_left (fun '((best_idx, b_acc), (curr_idx, best_val)) val =>
          match b_acc with
          | fz => ((best_idx, fz), (fs curr_idx, best_val))
          | fs b' =>
              match prob_le_b best_val val b' with
              | (true, b'') => ((fs curr_idx, b''), (fs curr_idx, val))
              | (false, b'') => ((best_idx, b''), (fs curr_idx, best_val))
              end
          end
        ) rest ((fz, b), (fz, first))
      in (best_idx, b_final)
  end.

(******************************************************************************)
(* FIBER INTERSECTION                                                         *)
(******************************************************************************)

Record FiberIntersection := {
  fiber1 : Fiber;
  fiber2 : Fiber;
  intersection_point : Coordinate;
  intersection_strength : FinProb;
  intersection_budget : Budget
}.

Definition fibers_intersect_b (f1 f2 : Fiber) (b : Budget) 
  : (option Coordinate * Budget) :=
  match b with
  | fz => (None, fz)
  | fs b' =>
      match fin_eq_b (fiber_axis f1) (fiber_axis f2) b' with
      | (true, b1) => (None, b1)
      | (false, b1) => (Some (fiber_anchor f1), b1)
      end
  end.

(******************************************************************************)
(* SUPERDIAGONAL COORDINATE - Pattern match on depth, NO NAT                 *)
(******************************************************************************)

Definition make_superdiag_coord (idx : Fin) (depth : Fin) : Coordinate :=
  match depth with
  | fz => []
  | fs fz => [idx]
  | fs (fs fz) => [idx; idx]
  | fs (fs (fs fz)) => [idx; idx; idx]
  | fs (fs (fs (fs fz))) => [idx; idx; idx; idx]
  | fs (fs (fs (fs (fs fz)))) => [idx; idx; idx; idx; idx]
  | fs (fs (fs (fs (fs (fs fz))))) => [idx; idx; idx; idx; idx; idx]
  | fs (fs (fs (fs (fs (fs (fs fz)))))) => [idx; idx; idx; idx; idx; idx; idx]
  | fs (fs (fs (fs (fs (fs (fs (fs _))))))) => [idx; idx; idx; idx; idx; idx; idx; idx]
  end.

Definition near_superdiagonal_b (coord : Coordinate) (tolerance : Fin) (b : Budget)
  : (bool * Budget) :=
  match superdiag_distance coord b with
  | (dist, b') => le_fin_b dist tolerance b'
  end.

(******************************************************************************)
(* RANK-1 DECOMPOSITION                                                       *)
(******************************************************************************)

Record Rank1Decomposition := {
  representative_fiber : Fiber;
  peak_location : Fin;
  reuse_count : Fin;
  symmetry_budget : Budget
}.

Definition make_rank1_b (f : Fiber) (reuse : Fin) (b : Budget) 
  : (Rank1Decomposition * Budget) :=
  match find_fiber_peak f b with
  | (peak, b') =>
      ({| representative_fiber := f;
          peak_location := peak;
          reuse_count := reuse;
          symmetry_budget := b' |}, b')
  end.

(******************************************************************************)
(* RANK-2 DECOMPOSITION                                                       *)
(******************************************************************************)

Record Rank2Decomposition := {
  current_fiber : Fiber;
  perturbed_fiber : Fiber;
  delta : Fin;
  intersection_matrix : list (list FinProb);
  rank2_budget : Budget
}.

Definition make_rank2_b (f_current : Fiber) (delta : Fin) (b : Budget)
  : (option Rank2Decomposition * Budget) :=
  match b with
  | fz => (None, fz)
  | fs b' =>
      let perturbed_anchor := 
        match fiber_anchor f_current with
        | [] => []
        | i :: rest => 
            let i_plus_delta := fst (add_fin_b i delta b') in
            i_plus_delta :: rest
        end in
      let f_perturbed := {| 
        fiber_values := fiber_values f_current;
        fiber_axis := fiber_axis f_current;
        fiber_anchor := perturbed_anchor;
        fiber_budget := b'
      |} in
      let default_prob := (fs fz, fs (fs fz)) in
      let val1 := match fiber_at f_current fz with
                  | Some v => v
                  | None => default_prob
                  end in
      let val2 := match fiber_at f_perturbed fz with
                  | Some v => v
                  | None => default_prob
                  end in
      let intersection := [[val1; val2]] in
      (Some {| current_fiber := f_current;
              perturbed_fiber := f_perturbed;
              delta := delta;
              intersection_matrix := intersection;
              rank2_budget := b' |}, b')
  end.

(******************************************************************************)
(* TENSOR NAVIGATION - Using fold_left with counter                          *)
(******************************************************************************)

Definition sample_1d_b (t : Tensor1D) (idx : Fin) (b : Budget) 
  : (option FinProb * Budget) :=
  match b with
  | fz => (None, fz)
  | fs b' =>
      snd (fold_left (fun '(curr_idx, (result, b_acc)) val =>
        match result with
        | Some _ => (fs curr_idx, (result, b_acc))
        | None =>
            match b_acc with
            | fz => (fs curr_idx, (None, fz))
            | fs b'' =>
                match fin_eq_b curr_idx idx b'' with
                | (true, b''') => (fs curr_idx, (Some val, b'''))
                | (false, b''') => (fs curr_idx, (None, b'''))
                end
            end
        end
      ) t (fz, (None, b')))
  end.

Definition extract_fiber_2d_b (t : Tensor2D) (fixed_idx : Fin) (b : Budget)
  : (option Tensor1D * Budget) :=
  match b with
  | fz => (None, fz)
  | fs b' =>
      snd (fold_left (fun '(curr_idx, (result, b_acc)) row =>
        match result with
        | Some _ => (fs curr_idx, (result, b_acc))
        | None =>
            match b_acc with
            | fz => (fs curr_idx, (None, fz))
            | fs b'' =>
                match fin_eq_b curr_idx fixed_idx b'' with
                | (true, b''') => (fs curr_idx, (Some row, b'''))
                | (false, b''') => (fs curr_idx, (None, b'''))
                end
            end
        end
      ) t (fz, (None, b')))
  end.

(******************************************************************************)
(* FIBER COMPARISON - Using fold_left                                        *)
(******************************************************************************)

Definition compare_fibers_b (f1 f2 : list FinProb) (b : Budget) : (bool * Budget) :=
  let '(c1, c2, b_final) := 
    fold_left (fun '(count1, count2, b_acc) '(v1, v2) =>
      match b_acc with
      | fz => (count1, count2, fz)
      | fs b' =>
          match prob_le_b v1 v2 b' with
          | (true, b'') => (count1, fs count2, b'')
          | (false, b'') => (fs count1, count2, b'')
          end
      end
    ) (combine f1 f2) (fz, fz, b)
  in le_fin_b c2 c1 b_final.

(******************************************************************************)
(* TENSOR CONSTRUCTION                                                        *)
(******************************************************************************)

Definition repeat_coord (val : Fin) (count : Fin) : Coordinate :=
  match count with
  | fz => []
  | fs fz => [val]
  | fs (fs fz) => [val; val]
  | fs (fs (fs fz)) => [val; val; val]
  | fs (fs (fs (fs fz))) => [val; val; val; val]
  | fs (fs (fs (fs (fs fz)))) => [val; val; val; val; val]
  | fs (fs (fs (fs (fs (fs fz))))) => [val; val; val; val; val; val]
  | fs (fs (fs (fs (fs (fs (fs fz)))))) => [val; val; val; val; val; val; val]
  | fs (fs (fs (fs (fs (fs (fs (fs _))))))) => [val; val; val; val; val; val; val; val]
  end.

Definition make_fiber (vals : list FinProb) (axis : Fin) 
                     (anchor : Coordinate) (b : Budget) : Fiber :=
  {| fiber_values := vals;
     fiber_axis := axis;
     fiber_anchor := anchor;
     fiber_budget := b |}.

(******************************************************************************)
(* AGGREGATE OPERATIONS - Using fold_left                                    *)
(******************************************************************************)

Definition fiber_sum (f : Fiber) (b : Budget) : (FinProb * Budget) :=
  fold_left (fun '(acc, b_acc) v =>
    match b_acc with
    | fz => (acc, fz)
    | fs b' =>
        match add_prob_b acc v b' with
        | (sum, b'') => (sum, b'')
        end
    end
  ) (fiber_values f) ((fz, fs fz), b).

Definition fiber_count_above (f : Fiber) (threshold : FinProb) (b : Budget) 
  : (Fin * Budget) :=
  fold_left (fun '(count, b_acc) v =>
    match b_acc with
    | fz => (count, fz)
    | fs b' =>
        match prob_le_b threshold v b' with
        | (true, b'') => (fs count, b'')
        | (false, b'') => (count, b'')
        end
    end
  ) (fiber_values f) (fz, b).

Definition fiber_map (f : Fiber) (op : FinProb -> Budget -> (FinProb * Budget)) 
                    (b : Budget) : (list FinProb * Budget) :=
  fold_left (fun '(acc, b_acc) v =>
    match b_acc with
    | fz => (acc, fz)
    | fs b' =>
        match op v b' with
        | (v', b'') => (v' :: acc, b'')
        end
    end
  ) (fiber_values f) ([], b).

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition Fiber_ext := Fiber.
Definition Rank1Decomposition_ext := Rank1Decomposition.
Definition Rank2Decomposition_ext := Rank2Decomposition.
Definition is_superdiagonal_ext := is_superdiagonal.
Definition find_fiber_peak_ext := find_fiber_peak.
Definition make_rank1_b_ext := make_rank1_b.
Definition make_rank2_b_ext := make_rank2_b.
Definition make_fiber_ext := make_fiber.
Definition fiber_sum_ext := fiber_sum.
Definition fiber_count_above_ext := fiber_count_above.

End Void_Tensor_Minimal.

(******************************************************************************)
(* PHILOSOPHY                                                                 *)
(*                                                                            *)
(* NO RECURSION. NO NAT. ONLY FOLDS AND EXPLICIT PATTERN MATCHING.           *)
(*                                                                            *)
(* Lists of specific lengths: explicitly write them out up to max depth.     *)
(* No conversion to/from nat. Pattern match on Fin up to the bound.          *)
(*                                                                            *)
(* This is BRUTALLY finite. 8 cases maximum. That's the universe.            *)
(******************************************************************************)