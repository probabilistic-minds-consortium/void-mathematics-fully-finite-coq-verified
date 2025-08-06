(******************************************************************************)
(* void_crisis_relocation.v - Crisis responses COST dearly                    *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module CrisisRelocation.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* CRISIS COSTS MORE - This is the philosophical heart                        *)
(******************************************************************************)

Definition CRISIS_MULTIPLIER : Fin := fs (fs (fs fz)).  (* 3x cost in crisis *)

(* Constants *)
Definition five : Fin := fs (fs (fs (fs (fs fz)))).
Definition nine : Fin := fs (fs (fs (fs five))).
Definition ten : Fin := fs nine.

(* Boolean helpers *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Simple modulo with budget *)
Definition mod_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match m, b with
  | fz, _ => (fz, b)  (* Undefined *)
  | _, fz => (fz, fz)  (* No budget *)
  | _, fs b' => 
      match le_fin_b n m b' with
      | (true, b'') => (n, b'')
      | (false, b'') => (fz, b'')  (* Simple: return 0 if n > m *)
      end
  end.

(* Average of two probabilities with budget *)
Definition avg_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match add_fin n1 n2 b with
  | (sum, b1) =>
      match max_fin_b d1 d2 b1 with
      | (max_d, b2) =>
          (* Simple average - not exact but saves budget *)
          ((sum, fs max_d), b2)
      end
  end.

(* Helper: find function with budget *)
Fixpoint find_b {A : Type} (f : A -> Budget -> (bool * Budget)) 
                (l : list A) (b : Budget) : (option A * Budget) :=
  match l, b with
  | [], _ => (None, b)
  | _, fz => (None, fz)
  | h :: t, fs b' =>
      match f h b' with
      | (true, b'') => (Some h, b'')
      | (false, b'') => find_b f t b''
      end
  end.

(* Different crisis response strategies *)
Inductive CrisisStrategy :=
  | Scatter        (* Jump to random location - costs medium *)
  | Cluster        (* Find others in crisis - costs high *)
  | Invert         (* Go opposite - costs low *)
  | Fragment       (* Split up - costs very high *)
  | Hibernate      (* Reduce activity - costs low *)
  | Merge          (* Combine - costs high *)
  | Explore        (* Small jumps - costs medium *)
  | Oscillate.     (* Alternate - costs medium *)

(* Strategy costs reflect desperation *)
Definition strategy_cost (s : CrisisStrategy) : Fin :=
  match s with
  | Scatter => fs (fs fz)         (* 2 *)
  | Cluster => fs (fs (fs fz))    (* 3 *)
  | Invert => fs fz               (* 1 *)
  | Fragment => fs (fs (fs (fs fz))) (* 4 - very expensive *)
  | Hibernate => fs fz            (* 1 *)
  | Merge => fs (fs (fs fz))      (* 3 *)
  | Explore => fs (fs fz)         (* 2 *)
  | Oscillate => fs (fs fz)       (* 2 *)
  end.

(* Choose strategy based on pattern and available budget *)
Definition choose_crisis_strategy (p : Pattern) (crisis_level : Fin) (b : Budget) 
  : (CrisisStrategy * Budget) :=
  match b with
  | fz => (Hibernate, fz)  (* No budget - hibernate only option *)
  | _ =>
      match fst (strength p), crisis_level with
      | fs fz, fz => 
          (* Weak + severe = scatter if affordable *)
          match le_fin_b (strategy_cost Scatter) b b with
          | (true, b') => (Scatter, b')
          | (false, b') => (Hibernate, b')
          end
      | fs fz, _ => (Cluster, b)
      | fs (fs fz), fz => (Fragment, b)
      | fs (fs fz), fs fz => (Merge, b)
      | fs (fs (fs _)), fz => (Invert, b)
      | fs (fs (fs _)), _ => (Explore, b)
      | _, _ => (Hibernate, b)
      end
  end.

(* Hash-based pseudo-random location with budget *)
Definition pseudo_random_location (p : Pattern) (seed : Fin) (b : Budget) 
  : (Fin * Budget) :=
  match add_fin (location p) seed b with
  | (h1, b1) =>
      match add_fin (fst (strength p)) h1 b1 with
      | (h2, b2) => mod_fin_b h2 ten b2
      end
  end.

(* Check if pattern is in crisis - costs budget *)
Definition is_in_crisis (p : Pattern) (b : Budget) : (bool * Budget) :=
  le_fin_b (fst (strength p)) (fs (fs fz)) b.

(* Find patterns in similar crisis with budget *)
Definition find_crisis_cluster (p : Pattern) (all_patterns : list Pattern) (b : Budget)
  : (list Fin * Budget) :=
  match b with
  | fz => ([], fz)
  | _ =>
      fold_left (fun acc p' =>
        match acc with
        | (locs, budget) =>
            match is_in_crisis p' budget with
            | (true, b') => (location p' :: locs, b')
            | (false, b') => (locs, b')
            end
        end
      ) all_patterns ([], b)
  end.

(* Invert location with budget *)
Definition invert_location (loc : Fin) (max_loc : Fin) (b : Budget) 
  : (Fin * Budget) :=
  sub_fin max_loc loc b.

(* Fragment costs heavily *)
Definition fragment_pattern (p : Pattern) (b : Budget) : (list Pattern * Budget) :=
  match b with
  | fz => ([p], fz)  (* Can't fragment without budget *)
  | fs fz => ([p], fs fz)  (* Not enough *)
  | fs (fs fz) => ([p], fs (fs fz))  (* Still not enough *)
  | fs (fs (fs fz)) => ([p], fs (fs (fs fz)))  (* Minimum for one fragment *)
  | fs (fs (fs (fs b'))) =>
      (* Can actually fragment *)
      let quarter_strength := (fs fz, fs (fs (fs (fs fz)))) in
      ([{| location := location p;
           strength := quarter_strength |};
        {| location := fs (location p);
           strength := quarter_strength |};
        {| location := fs (fs (location p));
           strength := quarter_strength |}], b')
  end.

(* Hibernate - cheap but weakening *)
Definition hibernate_pattern (p : Pattern) : Pattern :=
  {| location := location p;
     strength := (fs fz, fs (fs (fs (fs (fs (fs fz)))))) |}.

(* Merge attempt with budget *)
Definition merge_attempt (p : Pattern) (candidates : list Pattern) (b : Budget) 
  : (Pattern * Budget) :=
  match find_b (fun p' b => 
    match sub_fin (location p) (location p') b with
    | (diff, b') => le_fin_b diff (fs fz) b'
    end
  ) candidates b with
  | (Some partner, b') =>
      match avg_prob_b (strength p) (strength partner) b' with
      | (new_strength, b'') =>
          ({| location := location p;
              strength := new_strength |}, b'')
      end
  | (None, b') => (p, b')
  end.

(* Explore with budget *)
Definition explore_step (loc : Fin) (step_num : Fin) (b : Budget) 
  : (Fin * Budget) :=
  match step_num, b with
  | _, fz => (loc, fz)
  | fz, fs b' => (fs loc, b')
  | fs fz, fs b' => (fs (fs loc), b')
  | fs (fs fz), fs b' => 
      match loc with
      | fz => (fz, b')
      | fs loc' => (loc', b')
      end
  | _, _ => (loc, b)
  end.

(* Check if even with budget *)
Fixpoint even_fin_b (n : Fin) (b : Budget) : (bool * Budget) :=
  match n, b with
  | _, fz => (true, fz)  (* No budget - default true *)
  | fz, _ => (true, b)
  | fs fz, _ => (false, b)
  | fs (fs n'), fs b' => even_fin_b n' b'
  end.

(* Oscillate with budget *)
Definition oscillate_location (loc : Fin) (phase : Fin) (b : Budget) 
  : (Fin * Budget) :=
  match even_fin_b phase b with
  | (true, b') => (fz, b')
  | (false, b') => (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))), b')  (* 9 *)
  end.

(* Main crisis response - COSTS MULTIPLY IN CRISIS *)
Definition crisis_response (p : Pattern) (local_energy : Budget) 
                          (context : list Pattern) (global_phase : Fin) 
                          (b : Budget) : (list Pattern * Budget) :=
  let crisis_level := match local_energy with
                      | fz => fz           (* Severe *)
                      | fs fz => fs fz     (* Moderate *)
                      | _ => fs (fs fz)    (* Mild *)
                      end in
  
  (* Crisis multiplies costs! *)
  let crisis_budget := match crisis_level with
                       | fz => b  (* Severe crisis - no multiplier, already bad *)
                       | _ => 
                           match div_fin b CRISIS_MULTIPLIER b with
                           | (reduced, _, _) => reduced
                           end
                       end in
  
  match choose_crisis_strategy p crisis_level crisis_budget with
  | (strategy, b1) =>
      match sub_fin b1 (strategy_cost strategy) b1 with
      | (_, b2) =>
          match strategy with
          | Scatter => 
              match pseudo_random_location p global_phase b2 with
              | (new_loc, b3) =>
                  match decay_with_budget (strength p) b3 with
                  | (new_strength, b4) =>
                      ([{| location := new_loc; strength := new_strength |}], b4)
                  end
              end
          
          | Cluster =>
              match find_crisis_cluster p context b2 with
              | ([], b3) => ([p], b3)
              | (loc :: _, b3) => 
                  ([{| location := loc; strength := strength p |}], b3)
              end
          
          | Invert =>
              match invert_location (location p) ten b2 with
              | (new_loc, b3) =>
                  match decay_with_budget (strength p) b3 with
                  | (new_strength, b4) =>
                      ([{| location := new_loc; strength := new_strength |}], b4)
                  end
              end
          
          | Fragment => fragment_pattern p b2
          
          | Hibernate => ([hibernate_pattern p], b2)
          
          | Merge => 
              match merge_attempt p context b2 with
              | (merged, b3) => ([merged], b3)
              end
          
          | Explore =>
              match explore_step (location p) global_phase b2 with
              | (new_loc, b3) => 
                  ([{| location := new_loc; strength := strength p |}], b3)
              end
          
          | Oscillate =>
              match oscillate_location (location p) global_phase b2 with
              | (new_loc, b3) =>
                  match decay_with_budget (strength p) b3 with
                  | (new_strength, b4) =>
                      ([{| location := new_loc; strength := new_strength |}], b4)
                  end
              end
          end
      end
  end.

(* Crisis opportunity with budget *)
Definition crisis_opportunity (p1 p2 : Pattern) (crisis_level : Fin) (b : Budget) 
  : (option Pattern * Budget) :=
  match sub_fin (location p1) (location p2) b with
  | (dist, b1) =>
      match le_fin_b five dist b1 with
      | (true, b2) =>  (* Far apart *)
          match le_fin_b crisis_level (fs fz) b2 with
          | (true, b3) =>  (* High crisis *)
              (* Crisis allows unusual merger *)
              match add_fin (location p1) (location p2) b3 with
              | (sum_loc, b4) =>
                  match div_fin sum_loc (fs (fs fz)) b4 with
                  | (avg_loc, _, b5) =>
                      match avg_prob_b (strength p1) (strength p2) b5 with
                      | (avg_str, b6) =>
                          (Some {| location := avg_loc; strength := avg_str |}, b6)
                      end
                  end
              end
          | (false, b3) => (None, b3)
          end
      | (false, b2) => (None, b2)
      end
  end.

(* Crisis memory - patterns remember successful strategies *)
Record CrisisMemory := {
  pattern_id : Fin;
  successful_strategy : CrisisStrategy;
  survival_count : Fin;
  memory_budget : Budget  (* Memories need maintenance *)
}.

(* Update memory list with budget threading *)
Fixpoint update_memory_list (memories : list CrisisMemory) (target_id : Fin) 
                           (new_strategy : CrisisStrategy) (b : Budget) 
  : (list CrisisMemory * Budget) :=
  match memories, b with
  | [], _ => ([], b)
  | _, fz => (memories, fz)  (* No budget - return unchanged *)
  | m :: ms, fs b' =>
      match fin_eq_b (pattern_id m) target_id b' with
      | (true, b'') =>
          (* Found the target - update it *)
          let updated := {| pattern_id := pattern_id m;
                           successful_strategy := new_strategy;
                           survival_count := fs (survival_count m);
                           memory_budget := memory_budget m |} in
          match update_memory_list ms target_id new_strategy b'' with
          | (rest, b''') => (updated :: rest, b''')
          end
      | (false, b'') =>
          (* Not the target - keep as is *)
          match update_memory_list ms target_id new_strategy b'' with
          | (rest, b''') => (m :: rest, b''')
          end
      end
  end.

(* Learn from crisis - costs budget to remember *)
Definition update_crisis_memory (p : Pattern) (strategy : CrisisStrategy) 
                               (survived : bool) (memory : list CrisisMemory) 
                               (b : Budget) : (list CrisisMemory * Budget) :=
  match b with
  | fz => (memory, fz)  (* No budget - no learning *)
  | fs b' =>
      if survived then
        match find_b (fun m b => fin_eq_b (pattern_id m) (location p) b) memory b' with
        | (Some m, b'') =>
            (* Update existing memory *)
            update_memory_list memory (location p) strategy b''
        | (None, b'') =>
            (* Create new memory *)
            ({| pattern_id := location p;
                successful_strategy := strategy;
                survival_count := fs fz;
                memory_budget := b'' |} :: memory, b'')
        end
      else
        (memory, b')  (* Don't remember failures *)
  end.

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition CrisisStrategy_ext := CrisisStrategy.
Definition CrisisMemory_ext := CrisisMemory.
Definition crisis_response_ext := crisis_response.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Crisis is expensive. This models the reality that:
   
   1. DESPERATION COSTS - Panic responses waste resources
   2. CRISIS MULTIPLIES COSTS - Everything is harder in crisis
   3. FRAGMENTATION IS EXPENSIVE - Breaking apart costs dearly
   4. MEMORY NEEDS MAINTENANCE - Even remembering crisis costs
   5. COOPERATION EMERGES - Merge/cluster become rational despite cost
   
   The system shows that crisis creates a vicious cycle: less budget leads
   to worse decisions which cost more budget. Only hibernate (acceptance)
   or successful merge (cooperation) can break the cycle.
   
   This is thermodynamically honest: crisis states have higher entropy and
   thus require more energy to navigate. *)

End CrisisRelocation.