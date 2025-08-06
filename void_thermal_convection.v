(******************************************************************************)
(* void_thermal_convection.v - BUDGET-AWARE THERMAL DYNAMICS                 *)
(* Heat IS computational budget. Convection exhausts the system.             *)
(* Rising costs, sinking costs, circulation depletes - thermodynamics is real *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_pattern_thermo.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Thermal_Convection.

Import Void_Pattern.
Import Void_Pattern_Thermo.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* SYSTEM CONSTANTS - Given by the void                                      *)
(******************************************************************************)

Parameter rise_cost : Fin.
Parameter sink_cost : Fin.
Parameter circulation_cost : Fin.
Parameter layer_search_cost : Fin.
Parameter temperature_calc_cost : Fin.
Parameter emergency_multiplier : Fin.

Axiom rise_cost_spec : rise_cost = fs (fs fz).
Axiom sink_cost_spec : sink_cost = fs fz.
Axiom circulation_cost_spec : circulation_cost = fs (fs (fs fz)).
Axiom search_cost_spec : layer_search_cost = fs (fs fz).
Axiom temp_cost_spec : temperature_calc_cost = fs (fs fz).
Axiom emergency_spec : emergency_multiplier = fs (fs (fs (fs fz))).

(* Heat threshold parameter *)
Parameter heat_threshold : Fin.
Axiom heat_threshold_spec : heat_threshold = fs (fs fz).

(******************************************************************************)
(* CORE TYPES WITH BUDGET AWARENESS                                          *)
(******************************************************************************)

(* Thermal layer with energy budget *)
Record ThermalLayer := {
  layer_height : Fin;
  layer_temp : Fin;
  layer_patterns : list ThermalPattern;
  layer_budget : Budget;  (* Layer's computational resources *)
  convection_strength : FinProb
}.

(* Convection cell with REAL energy consumption *)
Record ConvectionCell := {
  hot_layer : Fin;
  cold_layer : Fin;
  circulation_rate : Fin;
  cell_budget : Budget  (* Actually gets consumed! *)
}.

(* Thermal system with global budget *)
Record ThermalSystem := {
  layers : list ThermalLayer;
  cells : list ConvectionCell;
  gravity_strength : Fin;
  system_budget : Budget;  (* Total system energy *)
  total_heat : Fin        (* Heat = spent budget *)
}.

(******************************************************************************)
(* HELPER OPERATIONS WITH BUDGET                                             *)
(******************************************************************************)

(* Boolean operations - free as structural *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Get pattern from ThermalPattern *)
Definition cold (tp : ThermalPattern) : Pattern := pattern tp.

(* Get heat from ThermalPattern *)
Definition heat (tp : ThermalPattern) : Fin := heat_generated tp.

(* Minimum with budget *)
Definition min_fin_b (n m : Fin) (b : Budget) : (Fin * Budget) :=
  match le_fin_b n m b with
  | (true, b') => (n, b')
  | (false, b') => (m, b')
  end.

(******************************************************************************)
(* THERMAL OPERATIONS WITH BUDGET                                            *)
(******************************************************************************)

(* Check if pattern is hot enough to rise - costs budget *)
Definition exceeds_heat_threshold_b (h : Fin) (b : Budget) : (bool * Budget) :=
  le_fin_b heat_threshold h b.

(* Find cooler layer above - expensive search *)
Definition find_cool_layer_above_b (current : Fin) (layers : list ThermalLayer) (b : Budget)
  : (option Fin * Budget) :=
  match b with
  | fz => (None, fz)
  | _ =>
      match sub_fin b layer_search_cost b with
      | (_, b1) =>
          (* Search through layers *)
          fold_left (fun acc l =>
            match acc with
            | (Some found, b_acc) => (Some found, b_acc)  (* Already found *)
            | (None, b_acc) =>
                match b_acc with
                | fz => (None, fz)
                | fs b' =>
                    match le_fin_b current (layer_height l) b' with
                    | (above, b1) =>
                        match le_fin_b (layer_temp l) (fs fz) b1 with
                        | (cool, b2) =>
                            if andb above cool then
                              (Some (layer_height l), b2)
                            else
                              (None, b2)
                        end
                    end
                end
            end
          ) layers (None, b1)
      end
  end.

(* Find warmer layer below - expensive search *)
Definition find_warm_layer_below_b (current : Fin) (layers : list ThermalLayer) (b : Budget)
  : (option Fin * Budget) :=
  match b with
  | fz => (None, fz)
  | _ =>
      match sub_fin b layer_search_cost b with
      | (_, b1) =>
          fold_left (fun acc l =>
            match acc with
            | (Some found, b_acc) => (Some found, b_acc)
            | (None, b_acc) =>
                match b_acc with
                | fz => (None, fz)
                | fs b' =>
                    match le_fin_b (layer_height l) current b' with
                    | (below, b1) =>
                        match le_fin_b (fs fz) (layer_temp l) b1 with
                        | (warm, b2) =>
                            if andb below warm then
                              (Some (layer_height l), b2)
                            else
                              (None, b2)
                        end
                    end
                end
            end
          ) layers (None, b1)
      end
  end.

(* Thermal circulation - costs budget! *)
Definition thermal_circulation_b (tp : ThermalPattern) (sys : ThermalSystem)
  : (Fin * Budget) :=
  match system_budget sys with
  | fz => (location (cold tp), fz)  (* No budget - no movement *)
  | _ =>
      match exceeds_heat_threshold_b (heat tp) (system_budget sys) with
      | (hot_enough, b1) =>
          if hot_enough then
            (* Rise costs more than sinking *)
            match sub_fin b1 rise_cost b1 with
            | (_, b2) =>
                match find_cool_layer_above_b (location (cold tp)) (layers sys) b2 with
                | (Some new_layer, b3) => (new_layer, b3)
                | (None, b3) => (location (cold tp), b3)
                end
            end
          else
            (* Sinking is cheaper *)
            match sub_fin b1 sink_cost b1 with
            | (_, b2) =>
                match find_warm_layer_below_b (location (cold tp)) (layers sys) b2 with
                | (Some new_layer, b3) => (new_layer, b3)
                | (None, b3) => (location (cold tp), b3)
                end
            end
      end
  end.

(* Apply circulation to pattern - depletes pattern AND system *)
Definition circulate_pattern_b (tp : ThermalPattern) (sys : ThermalSystem)
  : (ThermalPattern * Budget) :=
  match thermal_circulation_b tp sys with
  | (new_loc, b1) =>
      match fin_eq_b new_loc (location (cold tp)) b1 with
      | (stayed, b2) =>
          if stayed then
            (* No movement - keep heat but lose budget *)
            ({| pattern := cold tp;
                heat_generated := heat tp;
                compute_budget := compute_budget tp |}, b2)
          else
            (* Movement dissipates heat AND strength *)
            match decay_with_budget (strength (cold tp)) b2 with
            | (new_strength, b3) =>
                let new_heat := match heat tp with
                               | fz => fz
                               | fs h => h
                               end in
                ({| pattern := {| location := new_loc;
                                 strength := new_strength |};
                    heat_generated := new_heat;
                    compute_budget := compute_budget tp |}, b3)
            end
      end
  end.

(* Update layer temperature - costs budget to compute *)
Definition update_layer_temperature_b (layer : ThermalLayer) : ThermalLayer :=
  match layer_budget layer with
  | fz => layer  (* No budget - frozen *)
  | _ =>
      match sub_fin (layer_budget layer) temperature_calc_cost (layer_budget layer) with
      | (_, b1) =>
          (* Calculate total heat - expensive *)
          let calc_heat := fold_left (fun acc tp =>
            match acc with
            | (total, b_acc) =>
                match b_acc with
                | fz => (total, fz)
                | fs b' => 
                    match add_fin total (heat tp) b' with
                    | (new_total, b'') => (new_total, b'')
                    end
                end
            end
          ) (layer_patterns layer) (fz, b1) in
          
          match calc_heat with
          | (total_heat, b2) =>
              match min_fin_b total_heat (fs (fs (fs fz))) b2 with
              | (capped_heat, b3) =>
                  {| layer_height := layer_height layer;
                     layer_temp := capped_heat;
                     layer_patterns := layer_patterns layer;
                     layer_budget := b3;
                     convection_strength := convection_strength layer |}
              end
          end
      end
  end.

(* Step convection cell - actually consumes energy! *)
Definition step_convection_cell_b (cell : ConvectionCell) : ConvectionCell :=
  match cell_budget cell with
  | fz => cell  (* No energy - frozen *)
  | _ =>
      match sub_fin (cell_budget cell) circulation_cost (cell_budget cell) with
      | (_, b') =>
          {| hot_layer := hot_layer cell;
             cold_layer := cold_layer cell;
             circulation_rate := circulation_rate cell;
             cell_budget := b' |}  (* Energy depleted! *)
      end
  end.

(******************************************************************************)
(* SYSTEM EVOLUTION WITH BUDGET                                              *)
(******************************************************************************)

(* Evolve thermal system - expensive operation *)
Definition evolve_thermal_system_b (sys : ThermalSystem) : ThermalSystem :=
  match system_budget sys with
  | fz => sys  (* System frozen - no budget *)
  | _ =>
      (* Update patterns - very expensive *)
      let update_layers := fold_left (fun acc layer =>
        match acc with
        | (updated_layers, sys_b) =>
            match sys_b with
            | fz => (layer :: updated_layers, fz)
            | _ =>
                (* Circulate each pattern in layer *)
                let circulate_all := fold_left (fun acc2 tp =>
                  match acc2 with
                  | (patterns, b) =>
                      match circulate_pattern_b tp 
                              {| layers := layers sys;
                                 cells := cells sys;
                                 gravity_strength := gravity_strength sys;
                                 system_budget := b;
                                 total_heat := total_heat sys |} with
                      | (new_tp, b') => (new_tp :: patterns, b')
                      end
                  end
                ) (layer_patterns layer) ([], sys_b) in
                
                match circulate_all with
                | (new_patterns, b1) =>
                    let updated_layer := 
                      update_layer_temperature_b
                        {| layer_height := layer_height layer;
                           layer_temp := layer_temp layer;
                           layer_patterns := new_patterns;
                           layer_budget := layer_budget layer;
                           convection_strength := decay (convection_strength layer) |} in
                    (updated_layer :: updated_layers, b1)
                end
            end
        end
      ) (layers sys) ([], system_budget sys) in
      
      match update_layers with
      | (new_layers, b_final) =>
          (* Update cells *)
          let new_cells := map step_convection_cell_b (cells sys) in
          
          (* System cools - heat dissipates *)
          let new_heat := match total_heat sys with
                          | fz => fz
                          | fs h => h
                          end in
          
          {| layers := new_layers;
             cells := new_cells;
             gravity_strength := gravity_strength sys;
             system_budget := b_final;
             total_heat := new_heat |}
      end
  end.

(******************************************************************************)
(* CRISIS OPERATIONS - COST MORE!                                            *)
(******************************************************************************)

(* Calculate turbulence - costs budget *)
Definition turbulence_level_b (sys : ThermalSystem) : (Fin * Budget) :=
  fold_left (fun acc cell =>
    match acc with
    | (turb, b) =>
        match b with
        | fz => (turb, fz)
        | fs b' =>
            match add_fin turb (circulation_rate cell) b' with
            | (new_turb, b'') => (new_turb, b'')
            end
        end
    end
  ) (cells sys) (fz, system_budget sys).

(* Check for thermal runaway - costs budget *)
Definition thermal_runaway_b (sys : ThermalSystem) : (bool * Budget) :=
  match turbulence_level_b sys with
  | (turb, b) => le_fin_b (fs (fs (fs fz))) turb b
  end.

(* Emergency cooling - VERY expensive! *)
Definition emergency_cooling_b (sys : ThermalSystem) : ThermalSystem :=
  match system_budget sys with
  | fz => sys  (* Can't afford emergency cooling! *)
  | _ =>
      (* Emergency operations cost MORE *)
      match mult_fin emergency_multiplier circulation_cost (system_budget sys) with
      | (emergency_cost, b1) =>
          match le_fin_b emergency_cost b1 b1 with
          | (false, _) => sys  (* Can't afford it *)
          | (true, b2) =>
              match sub_fin b2 emergency_cost b2 with
              | (_, b3) =>
                  (* Dump all heat - expensive! *)
                  {| layers := map (fun layer =>
                       {| layer_height := layer_height layer;
                          layer_temp := fz;
                          layer_patterns := map (fun tp =>
                            {| pattern := cold tp;
                               heat_generated := fz;
                               compute_budget := fz |})  (* Patterns exhausted *)
                            (layer_patterns layer);
                          layer_budget := fz;  (* Layers exhausted *)
                          convection_strength := (fs fz, fs (fs (fs (fs fz)))) |})
                       (layers sys);
                     cells := [];  (* All cells dead *)
                     gravity_strength := gravity_strength sys;
                     system_budget := b3;  (* Mostly depleted *)
                     total_heat := fz |}
              end
          end
      end
  end.

(******************************************************************************)
(* INITIALIZATION WITH BUDGET                                                *)
(******************************************************************************)

(* Create thermal gradient - costs budget *)
Definition create_thermal_gradient_b (num_layers : Fin) (b : Budget)
  : (list ThermalLayer * Budget) :=
  match num_layers, b with
  | fz, _ => ([], b)
  | fs fz, _ =>
      ([{| layer_height := fz;
           layer_temp := fs (fs fz);
           layer_patterns := [];
           layer_budget := b;
           convection_strength := half |}], b)
  | fs (fs fz), fs b' =>
      ([{| layer_height := fz;
           layer_temp := fs (fs fz);
           layer_patterns := [];
           layer_budget := b';
           convection_strength := half |};
        {| layer_height := fs fz;
           layer_temp := fz;
           layer_patterns := [];
           layer_budget := b';
           convection_strength := half |}], b')
  | _, _ => ([], b)  (* Can't create more layers *)
  end.

(******************************************************************************)
(* PHILOSOPHICAL NOTE                                                         *)
(******************************************************************************)

(* Thermal convection in void mathematics reveals thermodynamic truth:
   
   1. HEAT IS COMPUTATION - Heat isn't separate from budget; it IS spent
      budget. Every calculation generates heat, every movement dissipates it.
   
   2. CONVECTION COSTS - Rising costs more than sinking (fighting gravity).
      Circulation depletes cells until they freeze.
   
   3. CRISIS MULTIPLIES COST - Emergency cooling costs MORE than normal
      operation. Panic is expensive. The system can be too exhausted to
      save itself.
   
   4. LAYERS HAVE BUDGETS - Each layer has finite computational resources.
      Hot layers exhaust faster. Cold layers conserve but compute slowly.
   
   5. NO PERPETUAL MOTION - Convection cells consume their energy and die.
      The system inevitably approaches thermal death as budgets deplete.
   
   This models real thermodynamics: computation generates heat, heat drives
   convection, convection depletes energy, and everything tends toward
   cold stillness. The second law emerges from budget depletion. *)

End Void_Thermal_Convection.