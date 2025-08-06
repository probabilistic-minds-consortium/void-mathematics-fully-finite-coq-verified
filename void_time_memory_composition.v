(******************************************************************************)
(* void_time_memory_composition.v                                             *)
(* TIME with resolution + MEMORY with decay - EVERYTHING COSTS                *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Time_Memory_Composition.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* SYSTEM CONSTANTS - Given by the void                                      *)
(******************************************************************************)

Parameter base_obs_cost : Fin.
Axiom base_obs_cost_spec : base_obs_cost = fs (fs fz).

Parameter sync_cost : Fin.
Axiom sync_cost_spec : sync_cost = fs (fs fz).

Parameter fail_cost : Fin.
Axiom fail_cost_spec : fail_cost = fs (fs (fs fz)).

Parameter weak_threshold : FinProb.
Axiom weak_threshold_spec : weak_threshold = (fs fz, fs (fs (fs (fs fz)))).

Parameter minimal_sync : FinProb.
Axiom minimal_sync_spec : minimal_sync = (fs fz, fs (fs (fs (fs fz)))).

Parameter half_prob : FinProb.
Axiom half_prob_spec : half_prob = (fs fz, fs (fs fz)).

(******************************************************************************)
(* TIME - Observable Change COSTS                                             *)
(******************************************************************************)

(* A tick is evidence of observable change - proper constructor name *)
Inductive tick :=
  | Tick : State -> State -> tick.

(* Observer with finite capabilities and resolution *)
Record Observer := {
  obs_id : Fin;
  resolution : FinProb;        (* How finely we can observe *)
  obs_budget : Budget          (* Resources remaining *)
}.

(* Observation cost depends on resolution - finer resolution costs more *)
Definition observation_cost (o : Observer) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' => 
      (* Cost is proportional to resolution fineness *)
      match fst (resolution o) with
      | fz => (base_obs_cost, b')
      | fs _ => (fs base_obs_cost, b') (* higher resolution costs more *)
      end
  end.

(* Can this observer afford to observe? *)
Definition can_observe (o : Observer) (b : Budget) : (bool * Budget) :=
  match observation_cost o b with
  | (cost, b1) =>
      le_fin_b cost (obs_budget o) b1
  end.

(* Observe a change if possible - costs budget *)
Definition observe_change (o : Observer) (s1 s2 : State) (b : Budget)
  : (option tick * Observer * Budget) :=
  match can_observe o b with
  | (false, b1) => (None, o, b1)
  | (true, b1) =>
      match observation_cost o b1 with
      | (cost, b2) =>
          match sub_fin (obs_budget o) cost b2 with
          | (new_budget, b3) =>
              (Some (Tick s1 s2),
               {| obs_id := obs_id o;
                  resolution := resolution o;
                  obs_budget := new_budget |},
               b3)
          end
      end
  end.

(******************************************************************************)
(* MEMORY - Decaying Traces COST TO ACCESS                                   *)
(******************************************************************************)

(* A memory trace stores a tick with a strength *)
Record MemoryTrace := {
  remembered_tick : tick;
  strength : FinProb
}.

(* Create a new memory trace - costs budget *)
Definition new_trace (t : tick) (init : FinProb) (b : Budget) 
  : (MemoryTrace * Budget) :=
  match b with
  | fz => ({| remembered_tick := t; strength := (fz, fs fz) |}, fz) (* degraded *)
  | fs b' => ({| remembered_tick := t; strength := init |}, b')
  end.

(* Decay a single trace - now returns just the trace *)
Definition decay_trace (mt : MemoryTrace) : MemoryTrace :=
  let (n,d) := strength mt in
  match n with
  | fz => mt
  | fs fz => mt (* too weak to decay further *)
  | fs (fs n') =>
      {| remembered_tick := remembered_tick mt;
         strength := (fs n', d) |}
  end.

(* Decay with budget tracking for consistency *)
Definition decay_trace_b (mt : MemoryTrace) (b : Budget) : (MemoryTrace * Budget) :=
  match b with
  | fz => (mt, fz) (* no budget - no decay *)
  | fs b' => (decay_trace mt, b')
  end.

(* Check if trace is forgotten - returns just bool for backward compatibility *)
Definition trace_forgotten (mt : MemoryTrace) : bool :=
  match strength mt with
  | (fs fz, fs (fs (fs (fs _)))) => true   (* ≤ 1/4 *)
  | (fs fz, fs (fs (fs fz))) => true       (* 1/3 *)
  | (fs fz, fs (fs fz)) => false           (* 1/2 *)
  | _ => false
  end.

(* Budget version for internal use *)
Definition trace_forgotten_b (mt : MemoryTrace) (b : Budget) : (bool * Budget) :=
  match b with
  | fz => (false, fz) (* no budget - assume not forgotten *)
  | fs b' => (trace_forgotten mt, b')
  end.

(* A bounded memory bank *)
Record MemoryBank := {
  traces : list MemoryTrace;
  capacity : Fin;
  owner_resolution : FinProb
  (* Note: removed memory_budget to match void_memory_trace.v usage *)
}.

(* Count traces - costs budget *)
Fixpoint memory_count_fin_b (ts : list MemoryTrace) (b : Budget) 
  : (Fin * Budget) :=
  match ts, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: rs, fs b' =>
      match memory_count_fin_b rs b' with
      | (count, b'') => (fs count, b'')
      end
  end.

(* Store a new tick if under capacity - simplified for compatibility *)
Definition store_observation (mb : MemoryBank) (t : tick) : MemoryBank :=
  match traces mb with
  | traces =>
      {| traces := {| remembered_tick := t; 
                     strength := owner_resolution mb |} :: traces;
         capacity := capacity mb;
         owner_resolution := owner_resolution mb |}
  end.

(* Store with budget for proper tracking *)
Definition store_observation_b (mb : MemoryBank) (t : tick) (b : Budget) 
  : (MemoryBank * Budget) :=
  match memory_count_fin_b (traces mb) b with
  | (count, b1) =>
      match le_fin_b count (capacity mb) b1 with
      | (true, b2) =>
          match new_trace t (owner_resolution mb) b2 with
          | (newm, b3) =>
              ({| traces := newm :: traces mb;
                  capacity := capacity mb;
                  owner_resolution := owner_resolution mb |}, b3)
          end
      | (false, b2) => (mb, b2) (* at capacity *)
      end
  end.

(* Map with budget *)
Fixpoint map_b {A B : Type} (f : A -> Budget -> (B * Budget))
                            (l : list A) (b : Budget) : (list B * Budget) :=
  match l, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | x :: xs, fs b' =>
      match f x b' with
      | (y, b'') =>
          match map_b f xs b'' with
          | (ys, b''') => (y :: ys, b''')
          end
      end
  end.

(* Filter with budget *)
Fixpoint filter_b {A : Type} (f : A -> Budget -> (bool * Budget))
                             (l : list A) (b : Budget) : (list A * Budget) :=
  match l, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | x :: xs, fs b' =>
      match f x b' with
      | (true, b'') =>
          match filter_b f xs b'' with
          | (ys, b''') => (x :: ys, b''')
          end
      | (false, b'') => filter_b f xs b''
      end
  end.

(* Decay entire memory bank - costs budget *)
Definition decay_memory_bank_b (mb : MemoryBank) (b : Budget) : (MemoryBank * Budget) :=
  match b with
  | fz => (mb, fz) (* no budget - no decay *)
  | _ =>
      match map_b decay_trace_b (traces mb) b with
      | (decayed, b1) =>
          match filter_b trace_forgotten_b decayed b1 with
          | (remaining, b2) =>
              ({| traces := remaining;
                  capacity := capacity mb;
                  owner_resolution := owner_resolution mb |}, b2)
          end
      end
  end.

(******************************************************************************)
(* COMPOSITION - Finding Common Ground COSTS BOTH OBSERVERS                   *)
(******************************************************************************)

(* Distance between Fin values - costs budget *)
Definition dist_fin_b (x y : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b x y b with
  | (true, b1) => sub_fin y x b1
  | (false, b1) => sub_fin x y b1
  end.

(* State distance - costs budget *)
Definition state_distance (s1 s2 : State) (b : Budget) : (Fin * Budget) :=
  match s1, s2 with
  | (n1, b1), (n2, b2) =>
      match dist_fin_b n1 n2 b with
      | (d1, b') =>
          match dist_fin_b b1 b2 b' with
          | (d2, b'') => add_fin d1 d2 b''
          end
      end
  end.

(* Check tick similarity - costs budget *)
Definition ticks_similar (t1 t2 : tick) (tolerance : Fin) (b : Budget) 
  : (bool * Budget) :=
  match t1, t2 with
  | Tick s1 s2, Tick s1' s2' =>
      match state_distance s1 s1' b with
      | (d1, b1) =>
          match le_fin_b d1 tolerance b1 with
          | (within1, b2) =>
              if within1 then
                match state_distance s2 s2' b2 with
                | (d2, b3) =>
                    le_fin_b d2 tolerance b3
                end
              else (false, b2)
          end
      end
  end.

(* Find similar tick - costs budget *)
Fixpoint find_similar_tick_in_traces (t : tick) (traces : list MemoryTrace) 
                                    (tolerance : Fin) (b : Budget)
  : (option (tick * FinProb) * Budget) :=
  match traces, b with
  | [], _ => (None, b)
  | _, fz => (None, fz)
  | mt :: rest, fs b' =>
      match ticks_similar t (remembered_tick mt) tolerance b' with
      | (true, b'') => (Some (remembered_tick mt, strength mt), b'')
      | (false, b'') => find_similar_tick_in_traces t rest tolerance b''
      end
  end.

(* Synchronization result *)
Record SyncResult := {
  reference_tick1 : option tick;
  reference_tick2 : option tick;
  sync_quality : FinProb;
  observers_after : (Observer * Observer);  (* Updated observers *)
  remaining_budget : Budget
}.

(* Maximum with budget *)
Definition max_fin_b (x y : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b x y b with
  | (true, b') => (y, b')
  | (false, b') => (x, b')
  end.

(* Synchronize observers - costs BOTH their budgets *)
Definition synchronize_observers (o1 o2 : Observer) (mb1 mb2 : MemoryBank) (b : Budget)
  : SyncResult :=
  match max_fin_b (fst (resolution o1)) (fst (resolution o2)) b with
  | (tolerance, b1) =>
      match traces mb1 with
      | [] => 
          (* No memories - minimal sync *)
          {| reference_tick1 := None;
             reference_tick2 := None;
             sync_quality := minimal_sync;
             observers_after := (o1, o2);
             remaining_budget := b1 |}
      | mt :: _ =>
          (* Try to find similar tick in o2's memory *)
          match find_similar_tick_in_traces (remembered_tick mt) 
                                           (traces mb2) tolerance b1 with
          | (Some (t2, strength2), b2) =>
              (* Found similar memories! Charge both observers *)
              match sub_fin (obs_budget o1) sync_cost b2 with
              | (new_b1, b3) =>
                  match sub_fin (obs_budget o2) sync_cost b3 with
                  | (new_b2, b4) =>
                      {| reference_tick1 := Some (remembered_tick mt);
                         reference_tick2 := Some t2;
                         sync_quality := half_prob; (* use system constant *)
                         observers_after := 
                           ({| obs_id := obs_id o1;
                               resolution := resolution o1;
                               obs_budget := new_b1 |},
                            {| obs_id := obs_id o2;
                               resolution := resolution o2;
                               obs_budget := new_b2 |});
                         remaining_budget := b4 |}
                  end
              end
          | (None, b2) =>
              (* No similar memories - higher cost *)
              match sub_fin (obs_budget o1) fail_cost b2 with
              | (new_b1, b3) =>
                  match sub_fin (obs_budget o2) fail_cost b3 with
                  | (new_b2, b4) =>
                      {| reference_tick1 := Some (remembered_tick mt);
                         reference_tick2 := None;
                         sync_quality := minimal_sync;
                         observers_after := 
                           ({| obs_id := obs_id o1;
                               resolution := resolution o1;
                               obs_budget := new_b1 |},
                            {| obs_id := obs_id o2;
                               resolution := resolution o2;
                               obs_budget := new_b2 |});
                         remaining_budget := b4 |}
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* PROPER INITIALIZATION - No values from nothing                             *)
(******************************************************************************)

(* Initial states with explicit budget cost *)
Definition make_state (n : Fin) (b : Fin) (budget : Budget) : (State * Budget) :=
  match budget with
  | fz => ((fz, fz), fz)
  | fs b' => ((n, b), b')
  end.

(* Initial observer with budget *)
Definition make_observer (id : Fin) (res : FinProb) (init_budget : Budget) (b : Budget) 
  : (Observer * Budget) :=
  match b with
  | fz => ({| obs_id := fz; 
              resolution := (fs fz, fs (fs fz)); 
              obs_budget := fz |}, fz)
  | fs b' => ({| obs_id := id; 
                 resolution := res; 
                 obs_budget := init_budget |}, b')
  end.

(* Initial memory bank *)
Definition make_memory_bank (cap : Fin) (res : FinProb) (b : Budget)
  : (MemoryBank * Budget) :=
  match b with
  | fz => ({| traces := []; 
              capacity := fz; 
              owner_resolution := (fs fz, fs (fs fz)) |}, fz)
  | fs b' => ({| traces := []; 
                 capacity := cap; 
                 owner_resolution := res |}, b')
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

(* The tick type and its constructor Tick are already available *)
(* No need to re-export them *)

(* Other exports remain the same *)
Definition Observer_ext := Observer.
Definition MemoryBank_ext := MemoryBank.
Definition MemoryTrace_ext := MemoryTrace.
Definition SyncResult_ext := SyncResult.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Time costs: Every observation depletes the observer. Fine resolution costs
   more because distinguishing subtle changes requires more effort.
   
   Memory costs: Accessing memories isn't free. Decay happens only when we
   pay to compute it. Searching through memories exhausts resources.
   
   Composition costs: When observers try to synchronize, BOTH pay the price.
   Failed synchronization costs more than success - discord is expensive.
   
   This models a universe where:
   - Observation changes the observer
   - Memory access has a price
   - Coordination depletes all participants
   - Nothing happens without resource expenditure
   
   Even time itself only passes when someone pays to observe it. *)

End Void_Time_Memory_Composition.