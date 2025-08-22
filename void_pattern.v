(******************************************************************************)
(* void_pattern.v - Pattern interference with heat tracking                   *)
(* Observation generates heat! Interference creates thermodynamic cost!       *)
(******************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.ZArith.ZArith.

Module Void_Pattern.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

(* Constants *)
Definition five : Fin := fs (fs (fs (fs (fs fz)))).
Definition ten : Fin := fs (fs (fs (fs (fs five)))).

(******************************************************************************)
(* BASIC TYPES                                                                *)
(******************************************************************************)

Record Pattern := {
  location : Fin;
  strength : FinProb
}.

Record Observer := {
  sensitivity : Fin;
  obs_budget : Budget;
  obs_heat : Heat  (* NEW: Accumulated heat from observations *)
}.

Definition strong_observer := {| sensitivity := fs fz; obs_budget := ten; obs_heat := fz |}.
Definition weak_observer := {| sensitivity := fs (fs (fs fz)); obs_budget := five; obs_heat := fz |}.

(******************************************************************************)
(* HELPERS WITH BUDGET                                                        *)
(******************************************************************************)

(* Generic list operations with budget *)
Fixpoint existsb_with_budget {A : Type} (f : A -> Budget -> (bool * Budget)) 
                             (l : list A) (b : Budget) : (bool * Budget) :=
  match l, b with
  | [], _ => (false, b)
  | _, fz => (false, fz)
  | x :: xs, fs b' =>
      match f x b' with
      | (true, b'') => (true, b'')
      | (false, b'') => existsb_with_budget f xs b''
      end
  end.

Fixpoint length_fin_with_budget {A : Type} (l : list A) (b : Budget) : (Fin * Budget) :=
  match l, b with
  | [], _ => (fz, b)
  | _, fz => (fz, fz)
  | _ :: t, fs b' => 
      match length_fin_with_budget t b' with
      | (len, b'') => (fs len, b'')
      end
  end.

(* Probability operations *)
Definition add_prob_with_budget (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  match b with
  | fz => (p1, fz)
  | fs b' =>
      match le_fin_b (fst p1) (fst p2) b' with
      | (true, b'') => (p2, b'')
      | (false, b'') => (p1, b'')
      end
  end.

(******************************************************************************)
(* CORE OPERATIONS WITH HEAT                                                 *)
(******************************************************************************)

(* Decay with heat - decay itself generates heat *)
Definition decay_with_heat (p : FinProb) (b : Budget) : (FinProb * Budget * Heat) :=
  match b with
  | fz => (p, fz, fz)  (* No budget - no decay, no heat *)
  | fs b' =>
      match p with
      | (fs (fs n), d) => ((fs n, d), b', fs fz)  (* Decay generates heat *)
      | other => (other, b', fs fz)  (* Even checking generates heat *)
      end
  end.

(* Pattern interference with heat tracking *)
Definition interfere_heat (p1 p2 : Pattern) (b : Budget) 
  : (list Pattern * Budget * Heat) :=
  match fin_eq_b3 (location p1) (location p2) b with
  | (BTrue, b1, h1) =>
      (* Same location - intense interference, lots of heat! *)
      match decay_with_heat (strength p1) b1 with
      | (s1', b2, h2) =>
          match decay_with_heat s1' b2 with
          | (s1'', b3, h3) =>
              match decay_with_heat (strength p2) b3 with
              | (s2', b4, h4) =>
                  match decay_with_heat s2' b4 with
                  | (s2'', b5, h5) =>
                      ([{| location := location p1; strength := s1'' |};
                        {| location := location p2; strength := s2'' |};
                        {| location := location p1; 
                           strength := (fs fz, fs (fs (fs (fs fz)))) |}], 
                       b5,
                       add_heat h1 (add_heat h2 (add_heat h3 (add_heat h4 h5))))
                  end
              end
          end
      end
  | (BFalse, b1, h1) =>
      (* Different locations - less heat *)
      match decay_with_heat (strength p1) b1 with
      | (s1', b2, h2) =>
          match decay_with_heat (strength p2) b2 with
          | (s2', b3, h3) =>
              ([{| location := location p1; strength := s1' |};
                {| location := location p2; strength := s2' |}], 
               b3,
               add_heat h1 (add_heat h2 h3))
          end
      end
  | (BUnknown, b1, h1) =>
      (* Can't determine - return minimal result *)
      ([p1; p2], b1, h1)
  end.

(* Observer sees pattern with heat generation *)
Definition can_see_heat (obs : Observer) (p : Pattern) 
  : (Bool3 * Observer) :=
  match le_fin_b3 (sensitivity obs) (fst (strength p)) (obs_budget obs) with
  | (result, b', h) => 
      (result, 
       {| sensitivity := sensitivity obs; 
          obs_budget := b';
          obs_heat := add_heat (obs_heat obs) h |})
  end.

(* Observation exhausts observer and generates heat *)
Definition observe_interference_heat (obs : Observer) (p1 p2 : Pattern) 
  : (list Pattern * Observer) :=
  match interfere_heat p1 p2 (obs_budget obs) with
  | (patterns, b', h) =>
      (patterns, 
       {| sensitivity := sensitivity obs; 
          obs_budget := b';
          obs_heat := add_heat (obs_heat obs) h |})
  end.

(******************************************************************************)
(* NEURONS WITH HEAT                                                         *)
(******************************************************************************)

Record Neuron := {
  neuron_id : Fin;
  threshold : FinProb;
  accumulated : FinProb;
  refractory : Fin;
  maintained_patterns : list Fin;
  neuron_budget : Budget;
  neuron_heat : Heat  (* NEW: Heat accumulated from firing *)
}.

(* Check if pattern location is maintained - generates heat *)
Fixpoint is_maintained_heat (locs : list Fin) (p : Fin) (b : Budget) 
  : (bool * Budget * Heat) :=
  match locs, b with
  | [], _ => (false, b, fz)
  | _, fz => (false, fz, fz)
  | h :: t, _ =>
      match fin_eq_b_heat h p b with
      | (true, b', h) => (true, b', h)
      | (false, b', h) => 
          match is_maintained_heat t p b' with
          | (res, b'', h') => (res, b'', add_heat h h')
          end
      end
  end.

(* Neuron observes pattern - generates heat *)
Definition observe_pattern_heat (n : Neuron) (p : Pattern) : Neuron :=
  match le_fin_b3 (fs fz) (refractory n) (neuron_budget n) with
  | (BTrue, _, _) => n  (* Refractory - no change *)
  | (_, b', h1) =>
      match is_maintained_heat (maintained_patterns n) (location p) b' with
      | (true, b'', h2) =>
          match prob_le_b3 (accumulated n) (strength p) b'' with
          | (res, b''', h3) =>
              let new_acc := match res with
                            | BTrue => strength p
                            | _ => accumulated n
                            end in
              {| neuron_id := neuron_id n;
                 threshold := threshold n;
                 accumulated := new_acc;
                 refractory := refractory n;
                 maintained_patterns := maintained_patterns n;
                 neuron_budget := b''';
                 neuron_heat := add_heat (neuron_heat n) 
                                        (add_heat h1 (add_heat h2 h3)) |}
          end
      | (false, b'', h2) => 
          {| neuron_id := neuron_id n;
             threshold := threshold n;
             accumulated := accumulated n;
             refractory := refractory n;
             maintained_patterns := maintained_patterns n;
             neuron_budget := b'';
             neuron_heat := add_heat (neuron_heat n) (add_heat h1 h2) |}
      end
  end.

(* Fire neuron - generates significant heat! *)
Definition fire_neuron_heat (n : Neuron) : (Neuron * option Pattern) :=
  match neuron_budget n with
  | fz => (n, None)
  | _ =>
      match refractory n with
      | fs _ => (n, None)  (* Still refractory *)
      | fz =>
          match prob_le_b3 (threshold n) (accumulated n) (neuron_budget n) with
          | (BTrue, b', h) =>
              (* FIRING! Generates lots of heat *)
              let firing_heat := fs (fs (fs h)) in  (* Triple the comparison heat *)
              ({| neuron_id := neuron_id n;
                  threshold := threshold n;
                  accumulated := (fs fz, snd (accumulated n));
                  refractory := fs (fs (fs fz));
                  maintained_patterns := maintained_patterns n;
                  neuron_budget := b';
                  neuron_heat := add_heat (neuron_heat n) firing_heat |},
               Some {| location := neuron_id n; strength := accumulated n |})
          | (_, b', h) =>
              ({| neuron_id := neuron_id n;
                  threshold := threshold n;
                  accumulated := accumulated n;
                  refractory := refractory n;
                  maintained_patterns := maintained_patterns n;
                  neuron_budget := b';
                  neuron_heat := add_heat (neuron_heat n) h |}, None)
          end
      end
  end.

(******************************************************************************)
(* BACKWARD COMPATIBILITY WRAPPERS                                           *)
(******************************************************************************)

(* Old decay function *)
Definition decay_with_budget (p : FinProb) (b : Budget) : (FinProb * Budget) :=
  match decay_with_heat p b with
  | (res, b', _) => (res, b')
  end.

(* Old interfere function *)
Definition interfere (p1 p2 : Pattern) (b : Budget) : (list Pattern * Budget) :=
  match interfere_heat p1 p2 b with
  | (patterns, b', _) => (patterns, b')
  end.

Definition interfere_with_budget := interfere.

(* Old can_see - collapse Bool3 to bool *)
Definition can_see (obs : Observer) (p : Pattern) : (bool * Observer) :=
  match can_see_heat obs p with
  | (res, obs') => (collapse3 res, obs')
  end.

Definition can_see_with_budget := can_see.

(* Old observe_interference *)
Definition observe_interference (obs : Observer) (p1 p2 : Pattern) 
  : (list Pattern * Observer) :=
  observe_interference_heat obs p1 p2.

(* Old is_maintained *)
Definition is_maintained (locs : list Fin) (p : Fin) (b : Budget) : (bool * Budget) :=
  match is_maintained_heat locs p b with
  | (res, b', _) => (res, b')
  end.

Definition is_maintained_with_budget (n : Neuron) (p : Pattern) (b : Budget)
  : (bool * Budget) :=
  is_maintained (maintained_patterns n) (location p) b.

(* Old observe_pattern *)
Definition observe_pattern (n : Neuron) (p : Pattern) : Neuron :=
  observe_pattern_heat n p.

Definition observe_pattern_with_budget := observe_pattern.

(* Old fire_neuron *)
Definition fire_neuron (n : Neuron) : (Neuron * option Pattern) :=
  fire_neuron_heat n.

Definition fire_neuron_with_budget := fire_neuron.

(* Should fire - for compatibility *)
Definition should_fire (n : Neuron) : bool :=
  match neuron_budget n with
  | fz => false
  | _ =>
      match refractory n with
      | fz => 
          match prob_le_b (threshold n) (accumulated n) (neuron_budget n) with
          | (result, _) => result
          end
      | _ => false
      end
  end.

Definition should_fire_with_budget (n : Neuron) : (bool * Budget) :=
  (should_fire n, neuron_budget n).

(* Process patterns *)
Fixpoint process_patterns (n : Neuron) (ps : list Pattern) : Neuron :=
  match ps with
  | [] => n
  | p :: rest =>
      match neuron_budget n with
      | fz => n
      | _ => process_patterns (observe_pattern_heat n p) rest
      end
  end.

Definition process_patterns_with_budget := process_patterns.

(* Tick refractory *)
Definition tick_refractory (n : Neuron) : Neuron :=
  {| neuron_id := neuron_id n;
     threshold := threshold n;
     accumulated := accumulated n;
     refractory := match refractory n with
                   | fz => fz
                   | fs r => r
                   end;
     maintained_patterns := maintained_patterns n;
     neuron_budget := neuron_budget n;
     neuron_heat := neuron_heat n |}.

Definition tick_refractory_with_budget := tick_refractory.

(******************************************************************************)
(* LAYERS - Complete version                                                  *)
(******************************************************************************)

Record Layer := {
  layer_id : Fin;
  neurons : list Neuron;
  input_patterns : list Pattern;
  output_patterns : list Pattern;
  layer_budget : Budget
}.

(* Process one neuron in layer context *)
Definition process_neuron_in_layer (n : Neuron) (inputs : list Pattern) : (Neuron * option Pattern) :=
  let n' := process_patterns n inputs in
  let n'' := tick_refractory n' in
  fire_neuron n''.

(* Layer step - simplified but complete *)
Definition layer_step (l : Layer) : Layer :=
  match layer_budget l with
  | fz => l
  | _ =>
      let results := map (fun n => process_neuron_in_layer n (input_patterns l)) (neurons l) in
      let new_neurons := map fst results in
      let new_patterns := fold_left (fun acc r =>
        match snd r with
        | Some p => p :: acc
        | None => acc
        end) results [] in
      {| layer_id := layer_id l;
         neurons := new_neurons;
         input_patterns := input_patterns l;
         output_patterns := new_patterns;
         layer_budget := match layer_budget l with
                        | fz => fz
                        | fs b => b
                        end |}
  end.

Definition layer_step_with_budget := layer_step.

(* Connect layers *)
Definition feed_forward (l1 l2 : Layer) : Layer :=
  {| layer_id := layer_id l2;
     neurons := neurons l2;
     input_patterns := output_patterns l1;
     output_patterns := output_patterns l2;
     layer_budget := layer_budget l2 |}.

(******************************************************************************)
(* EXPORTS FOR OTHER MODULES                                                  *)
(******************************************************************************)

Definition Pattern_ext := Pattern.
Definition Neuron_ext := Neuron.
Definition Layer_ext := Layer.
Definition Observer_ext := Observer.

(******************************************************************************)
(* HEAT CONSERVATION AXIOMS                                                  *)
(******************************************************************************)

Axiom pattern_heat_conservation : forall p1 p2 b patterns b' h,
  interfere_heat p1 p2 b = (patterns, b', h) -> 
  add_heat h b' = b.

(* Observation generates heat proportional to sensitivity *)
Axiom observation_heat_principle : forall obs p res obs',
  can_see_heat obs p = (res, obs') ->
  (fin_to_Z_PROOF_ONLY (obs_heat obs') >= fin_to_Z_PROOF_ONLY (obs_heat obs))%Z.


(* The pattern hierarchy theorem - axiom for now *)
Axiom strong_sees_more : forall p b,
  b <> fz ->
  fst (can_see {| sensitivity := fs (fs (fs fz)); obs_budget := b; obs_heat := fz |} p) = true ->
  fst (can_see {| sensitivity := fs fz; obs_budget := b; obs_heat := fz |} p) = true.

End Void_Pattern.