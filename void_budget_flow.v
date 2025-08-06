(******************************************************************************)
(* void_budget_flow.v - BUDGET-AWARE ECOLOGICAL DYNAMICS                     *)
(* Patterns seek niches, not just resources                                  *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Budget_Flow.

Import Void_Pattern.
Import Void_Arithmetic.
Import Void_Probability_Minimal.

(******************************************************************************)
(* HELPER FUNCTIONS                                                           *)
(******************************************************************************)

(* Distance between two Fin values - costs budget *)
Definition dist_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => sub_fin m n b'
  | (false, b') => sub_fin n m b'
  end.

(* Helper to create sequence of Fin values *)
Fixpoint seq_fin (n : Fin) : list Fin :=
  match n with
  | fz => []
  | fs n' => fz :: map fs (seq_fin n')
  end.

(* Length with budget - costs budget to count *)
Fixpoint length_fin_with_budget {A : Type} (l : list A) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: t, fs b' =>
      match length_fin_with_budget t b' with
      | (len, b'') => (fs len, b'')
      end
  end.

(* Simple modulo - costs budget *)
Definition modulo_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match m with
  | fz => (fz, b)
  | _ => 
      match le_fin_b n m b with
      | (true, b') => (n, b')
      | (false, b') => (fz, b')
      end
  end.

(******************************************************************************)
(* PATTERN ECOLOGY WITH BUDGET                                                *)
(******************************************************************************)

(* Budget-aware pattern type that carries its own fuel *)
Record BudgetedPattern := {
  pattern : Pattern;
  movement_budget : Budget
}.

(* Budget-aware layer that tracks its resource pool *)
Record BudgetedLayer := {
  layer : Layer;
  flow_budget : Budget
}.

(* Pattern preference based on strength - costs budget to compute *)
Definition pattern_preference_b (p : Pattern) (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      match fst (strength p) with
      | fz => (fz, b')  (* Dead patterns *)
      | fs fz => (fs fz, b')  (* Weak prefer low (1) *)
      | fs (fs fz) => (fs (fs (fs fz)), b')  (* Medium prefer medium (3) *)
      | _ => (fs (fs fz), b')  (* Strong prefer medium-low (2) *)
      end
  end.

(* Extract budget info from neurons - costs budget *)
Fixpoint neuron_budgets_b (neurons : list Neuron) (b : Budget) 
  : (list (Fin * Budget) * Budget) :=
  match neurons, b with
  | [], _ => ([], b)
  | _, fz => ([], fz)
  | n :: rest, fs b' =>
      let neuron_budget := match refractory n with
                          | fz => fs (fs (fs fz))
                          | fs _ => fz
                          end in
      match neuron_budgets_b rest b' with
      | (budgets, b'') => ((neuron_id n, neuron_budget) :: budgets, b'')
      end
  end.

(* Find complementary location - costs significant budget *)
Definition find_complementary_location_b (bp : BudgetedPattern) 
                                        (budgets : list (Fin * Budget))
  : (option Fin * Budget) :=
  match pattern_preference_b (pattern bp) (movement_budget bp) with
  | (pref, b1) =>
      (* Score each location - very expensive operation *)
      let score_location := fun entry b =>
        match entry with
        | (loc, budget) => 
            match dist_fin_b pref budget b with
            | (score, b') => ((loc, score), b')
            end
        end in
      
      (* Find best match through expensive comparisons *)
      match budgets, b1 with
      | [], _ => (None, b1)
      | (loc, bud) :: rest, _ =>
          match dist_fin_b pref bud b1 with
          | (init_score, b2) =>
              let find_best := fold_left (fun acc entry =>
                match acc with
                | ((best_loc, best_score), b_acc) =>
                    match score_location entry b_acc with
                    | ((new_loc, new_score), b') =>
                        match le_fin_b new_score best_score b' with
                        | (true, b'') => ((new_loc, new_score), b'')
                        | (false, b'') => ((best_loc, best_score), b'')
                        end
                    end
                end
              ) rest ((loc, init_score), b2) in
              match find_best with
              | ((best_loc, _), b_final) => (Some best_loc, b_final)
              end
          end
      end
  end.

(* Ecological move - patterns seek niches *)
Definition ecological_move_b (bp : BudgetedPattern) (bl : BudgetedLayer) 
  : (BudgetedPattern * BudgetedLayer) :=
  match neuron_budgets_b (neurons (layer bl)) (flow_budget bl) with
  | (budgets, b1) =>
      match find_complementary_location_b 
              {| pattern := pattern bp; movement_budget := b1 |} budgets with
      | (None, b2) => 
          (* No suitable location - stay put *)
          ({| pattern := pattern bp; movement_budget := b2 |},
           {| layer := layer bl; flow_budget := b2 |})
      | (Some target, b2) =>
          (* Check if weak pattern *)
          match le_fin_b (fst (strength (pattern bp))) (fs (fs fz)) b2 with
          | (true, b3) =>
              (* Weak patterns move without decay *)
              ({| pattern := {| location := target;
                               strength := strength (pattern bp) |};
                  movement_budget := b3 |},
               {| layer := layer bl; flow_budget := b3 |})
          | (false, b3) =>
              (* Strong patterns decay when moving *)
              match decay_with_budget (strength (pattern bp)) b3 with
              | (new_strength, b4) =>
                  ({| pattern := {| location := target;
                                   strength := new_strength |};
                      movement_budget := b4 |},
                   {| layer := layer bl; flow_budget := b4 |})
              end
          end
      end
  end.

(* Cooperative competition - costs budget to organize *)
Fixpoint cooperative_competition_b (patterns : list BudgetedPattern) 
                                   (available : Budget) 
                                   (org_budget : Budget)
  : list (BudgetedPattern * Budget) :=
  match patterns, org_budget with
  | [], _ => []
  | _, fz => []  (* No budget to organize *)
  | [p], _ => [(p, available)]
  | p1 :: p2 :: rest, fs b' =>
      (* Compare pattern strengths *)
      match dist_fin_b (fst (strength (pattern p1))) 
                       (fst (strength (pattern p2))) b' with
      | (distance, b1) =>
          match le_fin_b distance (fs fz) b1 with
          | (true, b2) =>
              (* Similar patterns share equally *)
              match div_fin available (fs (fs fz)) b2 with
              | (half, _, b3) =>
                  match add_fin half half b3 with
                  | (double_half, b4) =>
                      match sub_fin available double_half b4 with
                      | (remaining, b5) =>
                          (p1, half) :: (p2, half) :: 
                          cooperative_competition_b rest remaining b5
                      end
                  end
              end
          | (false, b2) =>
              (* Different patterns compete normally *)
              match div_fin available 
                    (fs (fs (fold_left (fun acc _ => fs acc) patterns fz))) b2 with
              | (share, _, b3) =>
                  map (fun p => (p, share)) (p1 :: p2 :: rest)
              end
          end
      end
  end.

(* Mutual aid between neurons - costs budget *)
Definition mutual_aid_b (n1 n2 : Neuron) (b : Budget) 
  : ((Neuron * Neuron) * Budget) :=
  match b with
  | fz => ((n1, n2), fz)
  | fs b1 =>
      let b1_budget := match refractory n1 with
                      | fz => fs (fs (fs fz))
                      | fs _ => fz
                      end in
      let b2_budget := match refractory n2 with
                      | fz => fs (fs (fs fz))
                      | fs _ => fz
                      end in
      
      (* Check if both poor *)
      match le_fin_b b1_budget (fs fz) b1 with
      | (poor1, b2) =>
          match le_fin_b b2_budget (fs fz) b2 with
          | (poor2, b3) =>
              if andb poor1 poor2 then
                ((n1, n2), b3)  (* No transfer between poor *)
              else
                (* Check wealth difference *)
                match sub_fin b1_budget b2_budget b3 with
                | (diff, b4) =>
                    match le_fin_b (fs (fs fz)) diff b4 with
                    | (true, b5) =>
                        (* Redistribute *)
                        match decay_with_budget (accumulated n2) b5 with
                        | (decayed_acc, b6) =>
                            (({| neuron_id := neuron_id n1;
                                 threshold := threshold n1;
                                 accumulated := accumulated n1;
                                 refractory := fz;
                                 maintained_patterns := maintained_patterns n1;
                                 neuron_budget := neuron_budget n1 |},
                              {| neuron_id := neuron_id n2;
                                 threshold := threshold n2;
                                 accumulated := decayed_acc;
                                 refractory := fz;
                                 maintained_patterns := maintained_patterns n2;
                                 neuron_budget := neuron_budget n2 |}), b6)
                        end
                    | (false, b5) => ((n1, n2), b5)
                    end
                end
          end
      end
  end.

(* Adapt neuron to patterns - expensive analysis *)
Definition adapt_neuron_to_patterns_b (n : Neuron) 
                                     (recent_patterns : list Pattern) 
                                     (b : Budget)
  : (Neuron * Budget) :=
  match recent_patterns, b with
  | [], _ => (n, b)
  | patterns, _ =>
      (* Calculate average strength - expensive *)
      let calc_avg := fold_left (fun acc p =>
        match acc with
        | (sum, b') =>
            match add_fin sum (fst (strength p)) b' with
            | (new_sum, b'') => (new_sum, b'')
            end
        end
      ) patterns (fz, b) in
      match calc_avg with
      | (avg_strength, b_final) =>
          ({| neuron_id := neuron_id n;
              threshold := (avg_strength, fs (fs (fs (fs fz))));
              accumulated := accumulated n;
              refractory := refractory n;
              maintained_patterns := maintained_patterns n;
              neuron_budget := neuron_budget n |}, b_final)
      end
  end.

(* Pattern alliance - costs budget to negotiate *)
Definition pattern_alliance_b (bp1 bp2 : BudgetedPattern) 
  : (option BudgetedPattern * Budget) :=
  (* Pool their movement budgets *)
  match add_fin (movement_budget bp1) (movement_budget bp2) 
                (movement_budget bp1) with
  | (pooled, b1) =>
      (* Check if at same location *)
      match fin_eq_b (location (pattern bp1)) (location (pattern bp2)) b1 with
      | (false, b2) => (None, b2)
      | (true, b2) =>
          (* Check if similar strength *)
          match dist_fin_b (fst (strength (pattern bp1))) 
                          (fst (strength (pattern bp2))) b2 with
          | (dist, b3) =>
              match le_fin_b dist (fs fz) b3 with
              | (false, b4) => (None, b4)
              | (true, b4) =>
                  (* Merge patterns *)
                  match add_prob_b (strength (pattern bp1)) 
                                   (strength (pattern bp2)) b4 with
                  | (sum_strength, b5) =>
                      match div_fin (fst sum_strength) (fs (fs fz)) b5 with
                      | (avg_n, _, b6) =>
                          (Some {| pattern := {| location := location (pattern bp1);
                                                strength := (avg_n, snd sum_strength) |};
                                  movement_budget := b6 |}, b6)
                      end
                  end
              end
          end
      end
  end.

(* Diversity bonus - costs budget to distribute *)
Definition diversity_bonus_b (bl : BudgetedLayer) (gift : Budget) 
  : BudgetedLayer :=
  let layer_neurons := neurons (layer bl) in
  match layer_neurons, flow_budget bl with
  | [], _ => bl  (* No neurons to bonus *)
  | _, fz => bl  (* No budget to give bonus *)
  | _, fs b' =>
      (* Count neurons - costs budget *)
      match length_fin_with_budget layer_neurons b' with
      | (len, b1) =>
          (* Select lucky neuron *)
          match modulo_b gift len b1 with
          | (index, b2) =>
              (* Update the lucky neuron *)
              let updated_neurons := map (fun (i_n : Fin * Neuron) =>
                match i_n with
                | (i, n) =>
                    match fin_eq_b i index b2 with
                    | (true, _) =>
                        {| neuron_id := neuron_id n;
                           threshold := threshold n;
                           accumulated := accumulated n;
                           refractory := fz;
                           maintained_patterns := maintained_patterns n;
                           neuron_budget := neuron_budget n |}
                    | (false, _) => n
                    end
                end
              ) (combine (seq_fin len) layer_neurons) in
              {| layer := {| layer_id := layer_id (layer bl);
                            neurons := updated_neurons;
                            input_patterns := input_patterns (layer bl);
                            output_patterns := output_patterns (layer bl);
                            layer_budget := layer_budget (layer bl) |};
                 flow_budget := b2 |}  (* Use the actual remaining budget *)
          end
      end
  end.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Budget Flow embodies ecological thinking in void mathematics:
   
   1. PATTERNS SEEK NICHES - Not just resources but complementary positions
      where their type thrives. Weak patterns prefer low-budget neurons.
   
   2. COOPERATION EMERGES - Similar patterns share resources rather than
      compete to extinction. Diversity is maintained through mutual aid.
   
   3. EVERY INTERACTION COSTS - Finding niches, forming alliances, even
      helping each other depletes finite resources. Nothing is free.
   
   4. ADAPTATION IS EXPENSIVE - Neurons adapting to patterns, patterns
      finding ecological fits - all require budget investment.
   
   5. RANDOMNESS MAINTAINS DIVERSITY - The diversity bonus doesn't go to
      the "best" but to random neurons, preventing monopolies.
   
   This creates a dynamic ecology where patterns and neurons co-evolve,
   seeking sustainable configurations rather than maximum extraction. *)

End Void_Budget_Flow.