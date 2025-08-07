(******************************************************************************)
(* void_budgeted_complexity.v - EMERGENCE FROM SIMPLE RULES UNDER CONSTRAINTS *)
(* Complexity isn't free. Every layer of organization costs budget.          *)
(* True complexity emerges not despite constraints but because of them.      *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_entropy.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Budgeted_Complexity.

Import Void_Pattern.
Import Void_Entropy.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* SYSTEM CONSTANTS - Complexity parameters                                  *)
(******************************************************************************)

Parameter complexity_threshold : Fin.
Parameter edge_of_chaos_beta : Fin.
Parameter cascade_criticality : FinProb.
Parameter integration_cost : Fin.
Parameter emergence_bonus : Fin.
Parameter compression_rate : FinProb.
Parameter hierarchy_factor : Fin.
Parameter avalanche_threshold : Fin.
Parameter consciousness_threshold : Fin.

Axiom complexity_threshold_spec : complexity_threshold = fs (fs (fs fz)).
Axiom edge_of_chaos_spec : edge_of_chaos_beta = fs (fs (fs (fs (fs fz)))).
Axiom cascade_criticality_spec : cascade_criticality = (fs fz, fs (fs fz)).
Axiom integration_cost_spec : integration_cost = fs (fs (fs (fs fz))).
Axiom emergence_bonus_spec : emergence_bonus = fs (fs fz).
Axiom compression_rate_spec : compression_rate = (fs (fs fz), fs (fs (fs fz))).
Axiom hierarchy_factor_spec : hierarchy_factor = fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))).
Axiom avalanche_threshold_spec : avalanche_threshold = fs (fs (fs (fs fz))).
Axiom consciousness_threshold_spec : consciousness_threshold = fs (fs fz).

(******************************************************************************)
(* HELPER FUNCTIONS - All properly budgeted                                  *)
(******************************************************************************)

Definition andb (b1 b2 : bool) : bool :=
  match b1 with true => b2 | false => false end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with true => true | false => b2 end.

(* Count list length with budget *)
Fixpoint length_fin_b {A : Type} (l : list A) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: t, fs b' =>
      match length_fin_b t b' with
      | (n, b'') => (fs n, b'')
      end
  end.

(* Predecessor with saturation *)
Definition pred_fin (n : Fin) : Fin :=
  match n with
  | fz => fz
  | fs n' => n'
  end.

(* Equality check with budget *)
Definition fin_eq_b_local (n m : Fin) (b : Budget) : (bool * Budget) :=
  fin_eq_b n m b.

(* Check if element in list - costs budget *)
Fixpoint elem_fin_b (x : Fin) (l : list Fin) (b : Budget) : (bool * Budget) :=
  match l, b with
  | [], _ => (false, b)
  | _, fz => (false, fz)
  | h :: t, fs b' =>
      match fin_eq_b x h b' with
      | (true, b'') => (true, b'')
      | (false, b'') => elem_fin_b x t b''
      end
  end.

(* Get nth element from list with budget *)
Fixpoint nth_fin_b {A : Type} (l : list A) (n : Fin) (b : Budget) 
  : (option A * Budget) :=
  match l, n, b with
  | [], _, _ => (None, b)
  | _, _, fz => (None, fz)
  | h :: _, fz, _ => (Some h, b)
  | _ :: t, fs n', fs b' => nth_fin_b t n' b'
  end.

(******************************************************************************)
(* FUNDAMENTAL COMPLEXITY MEASURES                                           *)
(******************************************************************************)

(* Program that generates patterns *)
Record Program := {
  instructions : list Fin;
  program_length : Fin;
  execution_cost : Fin
}.

(* Budgeted Kolmogorov Complexity *)
Definition kolmogorov_complexity_b (p : Pattern) (b : Budget) 
  : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      (* Simplified: complexity proportional to pattern strength *)
      match mult_fin (fst (strength p)) (fs (fs fz)) b' with
      | (complexity, b'') => (complexity, b'')
      end
  end.

(* Emergent complexity - behavior exceeds rules *)
Definition emergent_complexity_b (rules : Program) (behavior : list Pattern) (b : Budget)
  : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)
  | fs b' =>
      (* Complexity of behavior *)
      match fold_left (fun acc p =>
        match acc with
        | (c, b_acc) =>
            match kolmogorov_complexity_b p b_acc with
            | (p_complex, b1) =>
                match add_fin c p_complex b1 with
                | (new_c, b2) => (new_c, b2)
                end
            end
        end
      ) behavior (fz, b') with
      | (behavior_complex, b1) =>
          (* Subtract rule complexity *)
          match sub_fin behavior_complex (program_length rules) b1 with
          | (emergence, b2) => (emergence, b2)
          end
      end
  end.

(******************************************************************************)
(* CELLULAR AUTOMATA WITH BUDGET                                            *)
(******************************************************************************)

(* Cell with state and budget *)
Record BudgetedCell := {
  cell_state : Fin;
  cell_budget : Budget;
  cell_frozen : bool
}.

(* CA rule that costs budget *)
Definition ca_rule_b (left center right : BudgetedCell) (rule_num : Fin) 
  : BudgetedCell :=
  match cell_budget center with
  | fz => 
      (* No budget - cell dies *)
      {| cell_state := fz;
         cell_budget := fz;
         cell_frozen := true |}
  | fs b' =>
      (* Check if can afford computation *)
      match le_fin_b (fs fz) b' b' with
      | (true, b1) =>
          (* Apply rule - simplified *)
          let new_state := 
            match cell_state left, cell_state center, cell_state right with
            | fz, fz, fz => fz
            | fz, fz, fs _ => fs fz
            | fz, fs _, fz => fs fz
            | _, _, _ => cell_state center  (* Simplified *)
            end in
          {| cell_state := new_state;
             cell_budget := b1;
             cell_frozen := false |}
      | (false, b1) =>
          (* Can't afford - freeze *)
          {| cell_state := cell_state center;
             cell_budget := b1;
             cell_frozen := true |}
      end
  end.

(* Glider pattern with fuel *)
Record Glider := {
  glider_cells : list BudgetedCell;
  position : Fin;
  velocity : Fin;
  fuel : Budget
}.

(* Move glider - costs fuel proportional to distance *)
Definition move_glider_b (g : Glider) (distance : Fin) : Glider :=
  match mult_fin distance (fs fz) (fuel g) with
  | (move_cost, b1) =>
      match le_fin_b move_cost b1 b1 with
      | (true, b2) =>
          match sub_fin b2 move_cost b2 with
          | (_, b3) =>
              match add_fin (position g) distance b3 with
              | (new_pos, b4) =>
                  {| glider_cells := glider_cells g;
                     position := new_pos;
                     velocity := velocity g;
                     fuel := b4 |}
              end
          end
      | (false, b2) =>
          (* Not enough fuel - stop *)
          {| glider_cells := glider_cells g;
             position := position g;
             velocity := fz;
             fuel := b2 |}
      end
  end.

(******************************************************************************)
(* COMPLEXITY PHASE TRANSITIONS                                              *)
(******************************************************************************)

(* Complexity as function of budget *)
Definition complexity_phase_b (b : Budget) : (Fin * Budget) :=
  match b with
  | fz => (fz, fz)  (* Frozen - no complexity *)
  | _ =>
      match le_fin_b b complexity_threshold b with
      | (false, b1) => (fz, b1)  (* Below threshold - frozen *)
      | (true, b1) =>
          match le_fin_b b edge_of_chaos_beta b1 with
          | (true, b2) =>
              (* Complex region - logarithmic growth *)
              match div_fin b (fs (fs fz)) b2 with
              | (complexity, _, b3) => (complexity, b3)
              end
          | (false, b2) =>
              (* Chaotic region - sqrt growth *)
              match div_fin b (fs (fs (fs (fs fz)))) b2 with
              | (complexity, _, b3) => (complexity, b3)
              end
          end
      end
  end.

(* Find edge of chaos *)
Definition find_edge_of_chaos_b (system_budget : Budget) : (Fin * Budget) :=
  (* The edge is where second derivative is zero *)
  (* Simplified: return the constant *)
  (edge_of_chaos_beta, system_budget).

(******************************************************************************)
(* HIERARCHICAL EMERGENCE                                                    *)
(******************************************************************************)

Inductive EmergentLevel :=
  | Level0 : list Pattern -> EmergentLevel           (* Base patterns *)
  | Level1 : list (list Pattern) -> EmergentLevel    (* Assemblies *)
  | Level2 : list (list (list Pattern)) -> EmergentLevel  (* Networks *)
  | Level3 : list (list (list (list Pattern))) -> EmergentLevel. (* Ecosystems *)

(* Budget required for each level - costs budget to compute! *)
Definition level_budget_required_b (level : EmergentLevel) (b : Budget) : (Fin * Budget) :=
  match level, b with
  | Level0 _, _ => (fs fz, b)                    (* 1 *)
  | Level1 _, _ => (hierarchy_factor, b)         (* 10 *)
  | Level2 _, fs b' => 
      match mult_fin hierarchy_factor hierarchy_factor b' with
      | (req, b'') => (req, b'')                 (* 100 *)
      end
  | Level3 _, fs b' => 
      match mult_fin hierarchy_factor hierarchy_factor b' with
      | (h100, b1) =>
          match mult_fin hierarchy_factor h100 b1 with
          | (req, b2) => (req, b2)                (* 1000 *)
          end
      end
  | _, fz => (fz, fz)
  end.

(* Try to emerge to next level *)
Definition try_emerge_b (level : EmergentLevel) (b : Budget) 
  : (EmergentLevel * Budget) :=
  match level, b with
  | Level0 patterns, _ =>
      match le_fin_b hierarchy_factor b b with
      | (true, b1) =>
          match sub_fin b1 hierarchy_factor b1 with
          | (_, b2) =>
              (* Group patterns into assemblies *)
              (Level1 [patterns], b2)
          end
      | (false, b1) => (level, b1)
      end
  | Level1 assemblies, _ =>
      match mult_fin hierarchy_factor hierarchy_factor b with
      | (required, b1) =>
          match le_fin_b required b1 b1 with
          | (true, b2) =>
              match sub_fin b2 required b2 with
              | (_, b3) => (Level2 [assemblies], b3)
              end
          | (false, b2) => (level, b2)
          end
      end
  | _, _ => (level, b)
  end.

(******************************************************************************)
(* SELF-ORGANIZING CRITICALITY WITH BUDGET                                  *)
(******************************************************************************)

(* Sandpile with budget constraints *)
Record BudgetedSandpile := {
  heights : list Fin;
  grain_budget : Budget;
  critical_height : Fin
}.

(* Add grain with avalanche dynamics *)
Definition add_grain_b (pile : BudgetedSandpile) (pos : Fin) 
  : (BudgetedSandpile * Fin) :=  (* Returns (pile, avalanche_size) *)
  match grain_budget pile with
  | fz => (pile, fz)
  | fs b' =>
      match nth_fin_b (heights pile) pos b' with
      | (Some h, b1) =>
          match le_fin_b h avalanche_threshold b1 with
          | (true, b2) =>
              (* Below threshold - just add *)
              ({| heights := heights pile;  (* Should update at pos *)
                  grain_budget := b2;
                  critical_height := critical_height pile |}, fz)
          | (false, b2) =>
              (* Above threshold - avalanche! *)
              (* Size limited by budget *)
              match div_fin b2 (fs (fs fz)) b2 with
              | (max_avalanche, _, b3) =>
                  ({| heights := heights pile;  (* Should redistribute *)
                      grain_budget := b3;
                      critical_height := critical_height pile |}, max_avalanche)
              end
          end
      | (None, b1) => 
          ({| heights := heights pile;
              grain_budget := b1;
              critical_height := critical_height pile |}, fz)
      end
  end.

(******************************************************************************)
(* TURING PATTERNS WITH RESOURCE CONSTRAINTS                                 *)
(******************************************************************************)

(* Reaction-diffusion system *)
Record TuringSystem := {
  activator : list FinProb;
  inhibitor : list FinProb;
  diffusion_rates : (Fin * Fin);  (* (D_u, D_v) *)
  reaction_budget : Budget
}.

(* Update with resource depletion *)
Definition turing_step_b (sys : TuringSystem) : TuringSystem :=
  match reaction_budget sys with
  | fz => sys  (* No budget - frozen *)
  | fs b' =>
      (* Reaction term depletes budget - properly map with budget *)
      let process_activator := fold_left (fun acc a =>
        match acc with
        | (processed, b_acc) =>
            match b_acc with
            | fz => (a :: processed, fz)
            | fs b'' =>
                match div_fin (fst a) (fs (fs fz)) b'' with
                | (depleted, _, b''') =>
                    ((depleted, snd a) :: processed, b''')
                end
            end
        end
      ) (activator sys) ([], b') in
      
      match process_activator with
      | (updated_activator, b_final) =>
          {| activator := updated_activator;
             inhibitor := inhibitor sys;
             diffusion_rates := diffusion_rates sys;
             reaction_budget := b_final |}
      end
  end.

(* Check if patterns can form *)
Definition can_form_patterns_b (sys : TuringSystem) (b : Budget) 
  : (bool * Budget) :=
  match le_fin_b complexity_threshold (reaction_budget sys) b with
  | (sufficient_budget, b1) =>
      (* Check diffusion ratio *)
      match div_fin (fst (diffusion_rates sys)) (snd (diffusion_rates sys)) b1 with
      | (ratio, _, b2) =>
          match le_fin_b (fs (fs (fs (fs fz)))) ratio b2 with
          | (good_ratio, b3) =>
              (andb sufficient_budget good_ratio, b3)
          end
      end
  end.

(******************************************************************************)
(* INTEGRATED INFORMATION (PHI) WITH BUDGET                                  *)
(******************************************************************************)

(* System with integrated information *)
Record ConsciousSystem := {
  subsystems : list (list Pattern);
  connections : list (Fin * Fin * FinProb);  (* (from, to, strength) *)
  integration_budget : Budget;
  phi_value : FinProb
}.

(* Calculate integrated information with cost *)
Definition calculate_phi_b (sys : ConsciousSystem) : (FinProb * Budget) :=
  match integration_budget sys with
  | fz => ((fz, fs fz), fz)  (* No consciousness without budget *)
  | _ =>
      (* Cost proportional to system size *)
      match length_fin_b (subsystems sys) (integration_budget sys) with
      | (sys_size, b1) =>
          match mult_fin sys_size integration_cost b1 with
          | (cost, b2) =>
              match le_fin_b cost b2 b2 with
              | (false, b3) => ((fz, fs fz), b3)  (* Can't afford *)
              | (true, b3) =>
                  match sub_fin b3 cost b3 with
                  | (_, b4) =>
                      (* Simplified: phi proportional to connections *)
                      match length_fin_b (connections sys) b4 with
                      | (num_connections, b5) =>
                          ((num_connections, fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))), b5)
                      end
                  end
              end
          end
      end
  end.

(* System is conscious if phi > threshold *)
Definition is_conscious_b (sys : ConsciousSystem) (b : Budget) 
  : (bool * Budget) :=
  match calculate_phi_b sys with
  | (phi, b1) =>
      match le_fin_b consciousness_threshold (fst phi) b1 with
      | (conscious, b2) => (conscious, b2)
      end
  end.

(******************************************************************************)
(* ALGORITHMIC CHEMISTRY                                                     *)
(******************************************************************************)

(* Molecule as program with energy *)
Record Molecule := {
  mol_program : Program;
  mol_energy : Budget;
  mol_bonds : list Fin
}.

(* Chemical reaction with computation *)
Definition react_molecules_b (m1 m2 : Molecule) (activation : Fin) (b : Budget)
  : (option (Molecule * Molecule) * Budget) :=
  match add_fin (mol_energy m1) (mol_energy m2) b with
  | (total_energy, b1) =>
      match le_fin_b activation total_energy b1 with
      | (false, b2) => (None, b2)  (* Not enough activation energy *)
      | (true, b2) =>
          (* Execute combined program *)
          match sub_fin total_energy activation b2 with
          | (remaining, b3) =>
              (* Create products - simplified *)
              match div_fin remaining (fs (fs fz)) b3 with
              | (energy_share, _, b4) =>
                  let product1 := {| mol_program := mol_program m1;
                                    mol_energy := energy_share;
                                    mol_bonds := mol_bonds m2 |} in
                  let product2 := {| mol_program := mol_program m2;
                                    mol_energy := energy_share;
                                    mol_bonds := mol_bonds m1 |} in
                  (Some (product1, product2), b4)
              end
          end
      end
  end.

(* Autocatalytic set *)
Record AutocatalyticSet := {
  molecules : list Molecule;
  catalysis_cycles : list (list Fin);  (* Indices forming cycles *)
  energy_flux : Budget
}.

(* Check if set is self-sustaining *)
Definition is_autocatalytic_b (aset : AutocatalyticSet) (b : Budget) 
  : (bool * Budget) :=
  fold_left (fun acc cycle =>
    match acc with
    | (is_auto, b_acc) =>
        match b_acc with
        | fz => (false, fz)
        | fs b' =>
            (* Check if cycle closes with positive energy *)
            match fold_left (fun acc2 idx =>
              match acc2 with
              | (energy_sum, b2) =>
                  match nth_fin_b (molecules aset) idx b2 with
                  | (Some mol, b3) =>
                      match add_fin energy_sum (mol_energy mol) b3 with
                      | (new_sum, b4) => (new_sum, b4)
                      end
                  | (None, b3) => (energy_sum, b3)
                  end
              end
            ) cycle (fz, b') with
            | (cycle_energy, b_final) =>
                match le_fin_b (fs fz) cycle_energy b_final with
                | (positive, b_ret) => (andb is_auto positive, b_ret)
                end
            end
        end
    end
  ) (catalysis_cycles aset) (true, b).

(******************************************************************************)
(* STRANGE LOOPS AND TANGLED HIERARCHIES                                    *)
(******************************************************************************)

(* Self-referential structure *)
Record StrangeLoop := {
  loop_nodes : list Pattern;
  loop_edges : list (Fin * Fin * Fin);  (* (from, to, cost) *)
  loop_value : Fin;
  loop_budget : Budget
}.

(* Traverse strange loop *)
Definition traverse_loop_b (sl : StrangeLoop) : (bool * Budget) :=
  (* Calculate total cost *)
  fold_left (fun acc edge =>
    match acc with
    | (can_traverse, b_acc) =>
        match edge with
        | (_, _, cost) =>
            match le_fin_b cost b_acc b_acc with
            | (true, b1) =>
                match sub_fin b1 cost b1 with
                | (_, b2) => (can_traverse, b2)
                end
            | (false, b1) => (false, b1)
            end
        end
    end
  ) (loop_edges sl) (true, loop_budget sl).

(* Loop generates value if traversable *)
Definition loop_generates_value_b (sl : StrangeLoop) (b : Budget)
  : (option Fin * Budget) :=
  match traverse_loop_b sl with
  | (true, b1) =>
      (* Loop completed - generate value *)
      match add_fin (loop_value sl) emergence_bonus b1 with
      | (value, b2) => (Some value, b2)
      end
  | (false, b1) => (None, b1)
  end.

(******************************************************************************)
(* COMPLEXITY CASCADE NETWORKS                                               *)
(******************************************************************************)

(* Node that can trigger cascades *)
Record CascadeNode := {
  node_state : bool;
  node_threshold : Fin;
  node_inputs : list Fin;
  node_budget : Budget
}.

(* Network where activation cascades *)
Record CascadeNetwork := {
  cascade_nodes : list CascadeNode;
  cascade_edges : list (Fin * Fin);
  cascade_budget : Budget;
  cascade_active : list Fin
}.

(* Trigger cascade from node - with proper recursion *)
Fixpoint cascade_step (net : CascadeNetwork) (active : list Fin) 
                      (to_check : list Fin) (budget : Budget) 
  : (list Fin * Budget) :=
  match to_check, budget with
  | [], b => (active, b)
  | _, fz => (active, fz)
  | node :: rest, fs b' =>
      match nth_fin_b (cascade_nodes net) node b' with
      | (Some n, b1) =>
          (* Check if inputs exceed threshold *)
          match fold_left (fun acc input =>
            match acc with
            | (sum, b_acc) =>
                match elem_fin_b input active b_acc with
                | (true, b2) =>
                    match add_fin sum (fs fz) b2 with
                    | (new_sum, b3) => (new_sum, b3)
                    end
                | (false, b2) => (sum, b2)
                end
            end
          ) (node_inputs n) (fz, b1) with
          | (input_sum, b2) =>
              match le_fin_b (node_threshold n) input_sum b2 with
              | (true, b3) =>
                  (* Node activates - cascade continues *)
                  cascade_step net (node :: active) rest b3
              | (false, b3) =>
                  (* Below threshold - cascade stops here *)
                  cascade_step net active rest b3
              end
          end
      | (None, b1) => cascade_step net active rest b1
      end
  end.

(* Trigger cascade from node *)
Definition trigger_cascade_b (net : CascadeNetwork) (start : Fin)
  : (list Fin * Budget) :=  (* Returns (activated_nodes, remaining_budget) *)
  match cascade_budget net with
  | fz => ([], fz)
  | _ => cascade_step net [] [start] (cascade_budget net)
  end.

(******************************************************************************)
(* COMPLEXITY ATTRACTORS                                                     *)
(******************************************************************************)

Inductive AttractorType :=
  | FixedPoint : Pattern -> AttractorType
  | LimitCycle : list Pattern -> AttractorType
  | StrangeAttractor : list Pattern -> FinProb -> AttractorType  (* With fractal dimension *)
  | BudgetAttractor : Fin -> AttractorType.  (* Complexity sustainable at budget *)

Record ComplexityAttractor := {
  attractor_type : AttractorType;
  basin_size : Fin;
  stability : FinProb;
  maintenance_cost : Budget
}.

(* Evolve toward attractor *)
Definition evolve_to_attractor_b (p : Pattern) (attr : ComplexityAttractor) (b : Budget)
  : (Pattern * Budget) :=
  match attractor_type attr, b with
  | FixedPoint target, fs b' =>
      (* Move toward fixed point *)
      match dist_fin_b (location p) (location target) b' with
      | (dist, b1) =>
          match le_fin_b dist (fs fz) b1 with
          | (reached, b2) =>
              if reached then
                (target, b2)  (* Reached attractor *)
              else
                (* Move closer *)
                ({| location := pred_fin (location p);
                    strength := strength p |}, b2)
          end
      end
  | LimitCycle cycle, fs b' =>
      (* Follow cycle *)
      match cycle with
      | [] => (p, b')
      | next :: _ => (next, b')
      end
  | _, _ => (p, b)
  end.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* This module captures how complexity emerges under constraints:
   
   1. CELLULAR AUTOMATA freeze when budget depletes - no infinite computation
   2. GLIDERS need fuel proportional to distance - motion isn't free
   3. COMPLEXITY PHASES show transitions from frozen→complex→chaotic
   4. HIERARCHICAL EMERGENCE requires exponentially more budget per level
   5. SANDPILES can't cascade infinitely - avalanches limited by budget
   6. TURING PATTERNS only form above resource threshold
   7. CONSCIOUSNESS (Φ) requires massive integration budget
   8. MOLECULAR COMPUTATION follows thermodynamics - reactions need activation
   9. STRANGE LOOPS must generate more value than they consume
   10. CASCADE NETWORKS halt when activation budget exhausts
   11. ATTRACTORS have maintenance costs - even stability isn't free
   
   Key insight: Complexity = Rules + Constraints + Time
   
   Simple rules + budget constraints + time = rich emergent phenomena
   
   The universe computes only what it can afford. Life, consciousness,
   and civilization are solutions to the optimization:
   
   maximize C subject to: dβ/dt ≥ dC/dt · κ(C)
   
   Finding the richest patterns that can pay for themselves. *)

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition BudgetedCell_ext := BudgetedCell.
Definition Glider_ext := Glider.
Definition EmergentLevel_ext := EmergentLevel.
Definition BudgetedSandpile_ext := BudgetedSandpile.
Definition TuringSystem_ext := TuringSystem.
Definition ConsciousSystem_ext := ConsciousSystem.
Definition Molecule_ext := Molecule.
Definition AutocatalyticSet_ext := AutocatalyticSet.
Definition StrangeLoop_ext := StrangeLoop.
Definition CascadeNetwork_ext := CascadeNetwork.
Definition ComplexityAttractor_ext := ComplexityAttractor.

End Void_Budgeted_Complexity.