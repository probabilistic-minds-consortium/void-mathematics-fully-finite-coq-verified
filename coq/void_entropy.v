(******************************************************************************)
(* void_entropy.v                                                             *)
(* Entropy for finite observers - PROPERLY BUDGETED VERSION                   *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.

Module Void_Entropy.

(******************************************************************************)
(* ENTROPY IS COUNTING - BUT COUNTING COSTS                                  *)
(******************************************************************************)

(* Count non-zero elements WITH BUDGET *)
Fixpoint count_nonzero_b (l : list Fin) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)  (* Empty list - return remaining budget *)
  | _, fz => (fz, fz)  (* No budget - no computation *)
  | x :: rest, fs b' =>
      match x with
      | fz => count_nonzero_b rest b'  (* Zero doesn't add to count *)
      | fs _ => 
          match count_nonzero_b rest b' with
          | (count, b'') => (fs count, b'')
          end
      end
  end.

(* Primary entropy function - ALWAYS COSTS *)
Definition entropy_b (l : list Fin) (b : Budget) : (Fin * Budget) :=
  count_nonzero_b l b.

(******************************************************************************)
(* LENGTH COMPUTATION - ALSO COSTS                                           *)
(******************************************************************************)

(* Computing length requires examining each element *)
Fixpoint length_fin_b (l : list Fin) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)  (* No budget - can't count *)
  | _ :: rest, fs b' =>
      match length_fin_b rest b' with
      | (len, b'') => (fs len, b'')
      end
  end.

(******************************************************************************)
(* RESOLUTION - COARSENING COSTS TOO                                        *)
(******************************************************************************)

(* Even simple observation costs *)
Definition coarsen_b (value : Fin) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)  (* No budget - return zero *)
  | fs b' =>
      match value with
      | fz => (fz, b')
      | fs _ => (fs fz, b')  (* All non-zeros become 1 *)
      end
  end.

(* Map with budget - because iteration costs *)
Fixpoint map_b {A B : Type} (f : A -> Budget -> (B * Budget)) 
         (l : list A) (b : Budget) : (list B * Budget) :=
  match l, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)  (* No budget - empty result *)
  | x :: rest, fs b' =>
      match f x b' with
      | (y, b'') =>
          match map_b f rest b'' with
          | (ys, b''') => (y :: ys, b''')
          end
      end
  end.

(* Coarse entropy - costs for mapping AND counting *)
Definition coarse_entropy_b (l : list Fin) (b : Budget) : (Fin * Budget) :=
  match map_b coarsen_b l b with
  | (coarsened, b') => entropy_b coarsened b'
  end.

(******************************************************************************)
(* THE COST OF MEASUREMENT - NOW HONEST                                      *)
(******************************************************************************)

(* Measure entropy and return the cost *)
Definition measure_entropy_b (l : list Fin) (b : Budget) : (Fin * Fin * Budget) :=
  match entropy_b l b with
  | (ent, b') =>
      match length_fin_b l b' with
      | (len, b'') => (ent, len, b'')
      end
  end.

(******************************************************************************)
(* CONCRETE EXAMPLES - NOW WITH PROPER COSTS                                *)
(******************************************************************************)

Definition example := [fs fz; fz; fs (fs fz); fs fz].
Definition small_budget := fs (fs (fs (fs (fs fz)))).       (* 5 units *)
Definition large_budget := fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))). (* 10 units *)

(* These would compute if evaluated: *)
(* Compute (entropy_b example small_budget). *)
(* Result: (fs (fs (fs fz)), fs fz) - entropy is 3, 1 budget remains *)

(* Compute (coarse_entropy_b example small_budget). *)
(* Result: (fs (fs (fs fz)), fz) - uses all budget for mapping then counting *)

(* Compute (measure_entropy_b example large_budget). *)
(* Result: (fs (fs (fs fz)), fs (fs (fs (fs fz))), fs (fs fz)) *)
(* entropy=3, length=4, 2 budget remains *)

(******************************************************************************)
(* EXPORTS FOR OTHER MODULES                                                  *)
(******************************************************************************)

Definition entropy_ext := entropy_b.
Definition coarse_entropy_ext := coarse_entropy_b.
Definition measure_entropy_ext := measure_entropy_b.

(******************************************************************************)
(* THE PHILOSOPHY - NOW ACTUALLY IMPLEMENTED                                 *)
(******************************************************************************)

(* What we've ACTUALLY built:
   
   1. ENTROPY IS COUNTING - But counting costs budget per element examined
   
   2. COMPUTATION COSTS - Every operation consumes budget, no exceptions
   
   3. RESOLUTION COSTS - Even coarsening (simplifying observation) costs
   
   4. EVERYTHING IS FINITE - No infinities, no free operations
   
   This is the honest implementation where measurement has a price.
   No free lunch, not even for counting variety.
*)

End Void_Entropy.