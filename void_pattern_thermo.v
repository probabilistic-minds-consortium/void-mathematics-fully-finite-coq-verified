(******************************************************************************)
(* void_pattern_thermo.v - RADICAL REMAKE                                     *)
(* Heat IS computational budget. No free lunch, even in thermodynamics.       *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_pattern.
Require Import void_arithmetic.

Module Void_Pattern_Thermo.

Import Void_Pattern.
Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* METADATA OPERATIONS - These don't cost budget to avoid infinite regress    *)
(* Just like a thermometer's display doesn't heat up from showing temperature *)
(******************************************************************************)

(* Adding heat values is metadata bookkeeping, not computation *)
Fixpoint add_heat (h1 h2 : Fin) : Fin :=
  match h2 with
  | fz => h1
  | fs h2' => fs (add_heat h1 h2')
  end.

(* Comparing heat is also metadata *)
Fixpoint le_heat (h1 h2 : Fin) : bool :=
  match h1, h2 with
  | fz, _ => true
  | fs _, fz => false
  | fs h1', fs h2' => le_heat h1' h2'
  end.

(* Getting list length as metadata *)
Fixpoint length_fin {A : Type} (l : list A) : Fin :=
  match l with
  | [] => fz
  | _ :: t => fs (length_fin t)
  end.

(******************************************************************************)
(* FUNDAMENTAL INSIGHT: Heat = Spent Budget                                   *)
(* Every computation generates heat by consuming budget.                      *)
(* Heat is not a separate concept - it's the trace of computation.          *)
(******************************************************************************)

Record ThermalPattern := {
  pattern : Pattern;
  heat_generated : Fin;      (* Heat from past computations *)
  compute_budget : Budget    (* Remaining computational capacity *)
}.

(* Computing generates heat AND costs budget *)
Definition compute_with_heat (tp : ThermalPattern) (cost : Fin) 
  : option ThermalPattern :=
  match le_fin_b cost (compute_budget tp) (compute_budget tp) with
  | (true, b') =>
      match sub_fin cost (compute_budget tp) b' with
      | (_, b'') =>
          Some {| pattern := pattern tp;
                  heat_generated := add_heat (heat_generated tp) cost;
                  compute_budget := b'' |}
      end
  | (false, _) => None  (* Not enough budget *)
  end.

(* Thermal decay - heat makes patterns decay FASTER and costs budget *)
Definition thermal_decay (tp : ThermalPattern) : option ThermalPattern :=
  match compute_budget tp with
  | fz => None  (* No budget - pattern freezes *)
  | fs b' =>
      (* Cost depends on heat - hotter = more expensive to compute *)
      let cost := match heat_generated tp with
                  | fz => fs fz           (* Cold: cheap *)
                  | fs fz => fs (fs fz)   (* Warm: moderate *)
                  | _ => fs (fs (fs fz))  (* Hot: expensive *)
                  end in
      match compute_with_heat tp cost with
      | Some tp' =>
          (* Apply decay based on heat using BUDGETED operations *)
          match heat_generated tp with
          | fz => 
              (* No heat: no decay, but we still consumed budget for checking *)
              Some {| pattern := pattern tp;
                      heat_generated := heat_generated tp';
                      compute_budget := compute_budget tp' |}
          | fs fz => 
              (* Warm: single decay *)
              match decay_with_budget (strength (pattern tp)) (compute_budget tp') with
              | (new_strength, b_final) =>
                  Some {| pattern := {| location := location (pattern tp);
                                       strength := new_strength |};
                          heat_generated := heat_generated tp';
                          compute_budget := b_final |}
              end
          | _ => 
              (* Hot: double decay *)
              match decay_with_budget (strength (pattern tp)) (compute_budget tp') with
              | (strength_once, b_after_first) =>
                  match decay_with_budget strength_once b_after_first with
                  | (strength_twice, b_final) =>
                      Some {| pattern := {| location := location (pattern tp);
                                           strength := strength_twice |};
                              heat_generated := heat_generated tp';
                              compute_budget := b_final |}
                  end
              end
          end
      | None => None
      end
  end.

(******************************************************************************)
(* THERMAL FIELD - A universe with finite energy                             *)
(******************************************************************************)

Record ThermalField := {
  thermal_patterns : list ThermalPattern;
  total_energy : Budget;        (* Total available energy in system *)
  dissipated_heat : Fin        (* Heat lost to environment *)
}.

(* Measuring total heat costs budget! *)
Definition measure_total_heat (field : ThermalField) : (Fin * ThermalField) :=
  match total_energy field with
  | fz => (fz, field)  (* No energy to measure *)
  | fs b' =>
      match fold_left (fun acc tp =>
        match acc with
        | (heat_sum, budget_left) =>
            match budget_left with
            | fz => (heat_sum, fz)
            | fs b'' => (add_heat heat_sum (heat_generated tp), b'')
            end
        end
      ) (thermal_patterns field) (fz, b') with
      | (total_heat, remaining_budget) =>
          (total_heat, 
           {| thermal_patterns := thermal_patterns field;
              total_energy := remaining_budget;
              dissipated_heat := dissipated_heat field |})
      end
  end.

(******************************************************************************)
(* CRISIS FUSION - When energy is scarce, patterns merge desperately         *)
(******************************************************************************)

(* Crisis detection costs budget *)
Definition detect_crisis (field : ThermalField) : (bool * ThermalField) :=
  match total_energy field with
  | fz => (true, field)         (* No energy = definitely crisis *)
  | fs fz => (true, field)      (* Almost no energy = crisis *)
  | fs (fs fz) => 
      (* Check if patterns are dying - costs budget *)
      match thermal_patterns field with
      | [] => (false, {| thermal_patterns := [];
                        total_energy := fs fz;
                        dissipated_heat := dissipated_heat field |})
      | tp :: _ =>
          match strength (pattern tp) with
          | (fs fz, _) => (true, {| thermal_patterns := thermal_patterns field;
                                    total_energy := fs fz;
                                    dissipated_heat := dissipated_heat field |})
          | _ => (false, {| thermal_patterns := thermal_patterns field;
                           total_energy := fs fz;
                           dissipated_heat := dissipated_heat field |})
          end
      end
  | _ => (false, field)  (* Plenty of energy *)
  end.

(* Fusion costs ALL remaining budget of both patterns *)
Definition crisis_fuse (tp1 tp2 : ThermalPattern) : ThermalPattern :=
  {| pattern := {| location := location (pattern tp1);
                   strength := (fs fz, fs (fs (fs fz))) |}; (* Weak hybrid *)
     heat_generated := add_heat (add_heat (heat_generated tp1) (heat_generated tp2))
                                 (add_heat (compute_budget tp1) (compute_budget tp2));
     compute_budget := fz |}. (* Fusion exhausts both *)

(* System-wide crisis response *)
Definition crisis_response (field : ThermalField) : ThermalField :=
  match detect_crisis field with
  | (false, field') => field'  (* No crisis *)
  | (true, field') =>
      match thermal_patterns field' with
      | tp1 :: tp2 :: rest =>
          (* Check if patterns are co-located - costs budget! *)
          match fin_eq_b (location (pattern tp1)) (location (pattern tp2)) 
                        (total_energy field') with
          | (true, b') =>
              {| thermal_patterns := crisis_fuse tp1 tp2 :: rest;
                 total_energy := b';
                 dissipated_heat := fs (dissipated_heat field') |}
          | (false, b') => 
              {| thermal_patterns := thermal_patterns field';
                 total_energy := b';
                 dissipated_heat := dissipated_heat field' |}
          end
      | _ => field'  (* Not enough patterns to fuse *)
      end
  end.

(******************************************************************************)
(* EVOLUTION - The universe grinds forward, consuming energy                  *)
(******************************************************************************)

(* Distribute energy to patterns based on need *)
Definition distribute_energy (field : ThermalField) : ThermalField :=
  match thermal_patterns field with
  | [] => field
  | tps =>
      let n_patterns := length_fin tps in
      match div_fin (total_energy field) n_patterns (total_energy field) with
      | (energy_per_pattern, _, _) =>
          {| thermal_patterns := 
              map (fun tp => 
                {| pattern := pattern tp;
                   heat_generated := heat_generated tp;
                   compute_budget := energy_per_pattern |}) tps;
             total_energy := fz;  (* All distributed *)
             dissipated_heat := dissipated_heat field |}
      end
  end.

(* One evolution step *)
Definition evolve_thermal (field : ThermalField) : ThermalField :=
  (* First, handle crisis if needed *)
  let field' := crisis_response field in
  
  (* Then distribute remaining energy *)
  let field'' := distribute_energy field' in
  
  (* Apply thermal decay to all patterns *)
  let evolved_patterns := 
    fold_left (fun acc tp =>
      match thermal_decay tp with
      | Some tp' => tp' :: acc
      | None => acc  (* Pattern died from heat death *)
      end
    ) (thermal_patterns field'') [] in
  
  (* Collect dissipated heat *)
  let total_heat := 
    fold_left (fun h tp => add_heat h (heat_generated tp)) evolved_patterns fz in
  
  {| thermal_patterns := evolved_patterns;
     total_energy := fz;  (* All consumed in evolution *)
     dissipated_heat := add_heat (dissipated_heat field'') total_heat |}.

(******************************************************************************)
(* PHILOSOPHICAL CULMINATION                                                  *)
(******************************************************************************)
(* In this radical version:
   
   1. Heat is not a separate phenomenon - it's spent computational budget
   2. Every observation, every computation generates heat
   3. Hot systems compute less efficiently (heat increases computational cost)
   4. Crisis fusion represents the desperate creativity of exhausted systems
   5. The universe has finite total energy that decreases monotonically
   
   BUT: Heat tracking itself is metadata - it doesn't cost budget because
   otherwise we'd have infinite regress. This is like how a thermometer's
   display doesn't heat up from showing the temperature.
   
   This models computation as fundamentally thermodynamic: every thought 
   generates heat, every calculation brings the universe closer to heat death.
   
   Even the decay operation itself costs budget - in hot systems, you pay
   more just to compute how much things have decayed. The hotter the system,
   the more expensive it becomes to think about its own decay.
   
   Landauer's principle isn't just about bit erasure - it's about the 
   irreversible cost of ANY computation in a finite universe. *)

End Void_Pattern_Thermo.