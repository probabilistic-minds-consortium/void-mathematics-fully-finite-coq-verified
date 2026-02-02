(******************************************************************************)
(* void_perceptron.v                                                          *)
(* VOID NEURAL NETWORK - Learning through thermodynamic erosion               *)
(*                                                                            *)
(* "Learning is not optimization. Learning is credit assignment."             *)
(*                                                                            *)
(* No gradients. No backpropagation. No infinity. No Admitted.                *)
(******************************************************************************)

Require Import Coq.Init.Prelude.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import void_finite_minimal.
Require Import void_probability_minimal.

Import Void_Probability_Minimal.

Module Void_Perceptron.

(******************************************************************************)
(* SYNAPSE                                                                    *)
(* Conductance in (0,1): never fully open (1) or closed (0)                   *)
(******************************************************************************)

Record Synapse := mkSynapse {
  conductance : FinProb
}.

(******************************************************************************)
(* TRANSMISSION                                                               *)
(* Signal passes if conductance > 1/2, else blocked with heat                 *)
(******************************************************************************)

Definition transmit (input : Fin) (syn : Synapse) (b : Budget) 
  : (Fin * Fin * Budget * Heat) :=
  (* Returns: (output_signal, resistance_heat, remaining_budget, operation_heat) *)
  match b with
  | fz => (fz, fz, fz, fz)
  | fs b' =>
      match input with
      | fz => (fz, fz, b', fs fz)  (* No input = no output, 1 tick *)
      | fs _ =>
          let (num, den) := conductance syn in
          (* Check: 2*num > den? *)
          match mult_fin_heat num (fs (fs fz)) b' with
          | (doubled, b1, h1) =>
              match le_fin_b3 den doubled b1 with
              | (BTrue, b2, h2) => 
                  (* Open pipe - signal passes *)
                  (input, fz, b2, add_heat h1 h2)
              | (BFalse, b2, h2) =>
                  (* Closed pipe - blocked, generate resistance heat *)
                  match sub_saturate_b_heat den num b2 with
                  | (resistance, b3, h3) =>
                      (fz, resistance, b3, add_heat h1 (add_heat h2 h3))
                  end
              | (BUnknown, b2, h2) =>
                  (* Unknown - conservative block *)
                  (fz, fz, b2, add_heat h1 h2)
              end
          end
      end
  end.

(******************************************************************************)
(* NEURON                                                                     *)
(* Fixed size: 2 synapses (for AND gate). Explicit, no polymorphic lists.     *)
(******************************************************************************)

Record Neuron2 := mkNeuron2 {
  syn1 : Synapse;
  syn2 : Synapse;
  threshold : Fin
}.

(* Activation for 2-input neuron *)
Definition activate2 (n : Neuron2) (in1 in2 : Fin) (b : Budget)
  : (Fin * Budget * Heat) :=
  match transmit in1 (syn1 n) b with
  | (sig1, _, b1, h1) =>
      match transmit in2 (syn2 n) b1 with
      | (sig2, _, b2, h2) =>
          match add_fin_b_heat sig1 sig2 b2 with
          | (total, b3, h3) =>
              match le_fin_b3 (threshold n) total b3 with
              | (BTrue, b4, h4) =>
                  (fs fz, b4, add_heat h1 (add_heat h2 (add_heat h3 h4)))
              | (BFalse, b4, h4) =>
                  (fz, b4, add_heat h1 (add_heat h2 (add_heat h3 h4)))
              | (BUnknown, b4, h4) =>
                  (fz, b4, add_heat h1 (add_heat h2 (add_heat h3 h4)))
              end
          end
      end
  end.

(******************************************************************************)
(* ERROR                                                                      *)
(******************************************************************************)

Inductive Error := Undershoot | Match | Overshoot | EUnknown.

Definition compute_error (output target : Fin) (b : Budget) : (Error * Budget * Heat) :=
  match fin_eq_b3 output target b with
  | (BTrue, b', h) => (Match, b', h)
  | (BFalse, b', h1) =>
      match output, target with
      | fz, fs _ => (Undershoot, b', h1)
      | fs _, fz => (Overshoot, b', h1)
      | _, _ => (EUnknown, b', h1)
      end
  | (BUnknown, b', h) => (EUnknown, b', h)
  end.

(******************************************************************************)
(* LEARNING: ERODE / CONSTRICT                                                *)
(******************************************************************************)

Definition erode (syn : Synapse) (b : Budget) : (Synapse * Budget * Heat) :=
  match b with
  | fz => (syn, fz, fz)
  | fs b' =>
      let (num, den) := conductance syn in
      match num, den with
      | _, fz => (syn, b', fs fz)
      | _, fs fz => (syn, b', fs fz)
      | _, fs (fs den'') =>
          match le_fin_b3 (fs num) (fs den'') b' with
          | (BTrue, b'', h) => (mkSynapse (fs num, den), b'', h)
          | (_, b'', h) => (syn, b'', h)
          end
      end
  end.

Definition constrict (syn : Synapse) (b : Budget) : (Synapse * Budget * Heat) :=
  match b with
  | fz => (syn, fz, fz)
  | fs b' =>
      let (num, den) := conductance syn in
      match num with
      | fz => (syn, b', fs fz)
      | fs fz => (syn, b', fs fz)
      | fs (fs n'') => (mkSynapse (fs n'', den), b', fs fz)
      end
  end.

(******************************************************************************)
(* CREDIT PROPAGATION                                                         *)
(******************************************************************************)

Definition update_synapse (err : Error) (input : Fin) (syn : Synapse) (b : Budget)
  : (Synapse * Budget * Heat) :=
  match input with
  | fz => (syn, b, fz)
  | fs _ =>
      match err with
      | Undershoot => erode syn b
      | Match => erode syn b
      | Overshoot => constrict syn b
      | EUnknown => (syn, b, fz)
      end
  end.

Definition propagate2 (err : Error) (in1 in2 : Fin) (n : Neuron2) (b : Budget)
  : (Neuron2 * Budget * Heat) :=
  match update_synapse err in1 (syn1 n) b with
  | (new_syn1, b1, h1) =>
      match update_synapse err in2 (syn2 n) b1 with
      | (new_syn2, b2, h2) =>
          (mkNeuron2 new_syn1 new_syn2 (threshold n), b2, add_heat h1 h2)
      end
  end.

(******************************************************************************)
(* TRAINING STEP                                                              *)
(******************************************************************************)

Definition train_step2 (n : Neuron2) (in1 in2 target : Fin) (b : Budget)
  : (Neuron2 * Fin * Error * Budget * Heat) :=
  match activate2 n in1 in2 b with
  | (output, b1, h1) =>
      match compute_error output target b1 with
      | (err, b2, h2) =>
          match propagate2 err in1 in2 n b2 with
          | (new_n, b3, h3) =>
              (new_n, output, err, b3, add_heat h1 (add_heat h2 h3))
          end
      end
  end.

(******************************************************************************)
(* AND GATE EPOCH                                                             *)
(******************************************************************************)

Definition train_and_epoch (n : Neuron2) (b : Budget) 
  : (Neuron2 * Fin * Budget * Heat) :=
  match train_step2 n fz fz fz b with
  | (n1, out1, _, b1, h1) =>
      let c1 := match fin_eq_b3 out1 fz b1 with 
                | (BTrue, _, _) => fs fz | _ => fz end in
      match train_step2 n1 fz (fs fz) fz b1 with
      | (n2, out2, _, b2, h2) =>
          let c2 := match fin_eq_b3 out2 fz b2 with
                    | (BTrue, _, _) => fs fz | _ => fz end in
          match train_step2 n2 (fs fz) fz fz b2 with
          | (n3, out3, _, b3, h3) =>
              let c3 := match fin_eq_b3 out3 fz b3 with
                        | (BTrue, _, _) => fs fz | _ => fz end in
              match train_step2 n3 (fs fz) (fs fz) (fs fz) b3 with
              | (n4, out4, _, b4, h4) =>
                  let c4 := match fin_eq_b3 out4 (fs fz) b4 with
                            | (BTrue, _, _) => fs fz | _ => fz end in
                  match add_fin_b_heat c1 c2 b4 with
                  | (c12, b5, h5) =>
                      match add_fin_b_heat c12 c3 b5 with
                      | (c123, b6, h6) =>
                          match add_fin_b_heat c123 c4 b6 with
                          | (total_c, b7, h7) =>
                              (n4, total_c, b7, 
                               add_heat h1 (add_heat h2 (add_heat h3 
                               (add_heat h4 (add_heat h5 (add_heat h6 h7))))))
                          end
                      end
                  end
              end
          end
      end
  end.

(* Training loop *)
Fixpoint train_loop (fuel : Fin) (n : Neuron2) (b : Budget) 
  : (Neuron2 * Fin * Budget * Heat) :=
  match fuel with
  | fz => (n, fz, b, fz)
  | fs fuel' =>
      match b with
      | fz => (n, fz, fz, fz)
      | fs _ =>
          match train_and_epoch n b with
          | (new_n, correct, b', h1) =>
              match fin_eq_b3 correct (fs (fs (fs (fs fz)))) b' with
              | (BTrue, b'', h2) =>
                  (new_n, correct, b'', add_heat h1 h2)
              | (_, b'', h2) =>
                  match train_loop fuel' new_n b'' with
                  | (final_n, final_c, b_f, h_r) =>
                      (final_n, final_c, b_f, add_heat h1 (add_heat h2 h_r))
                  end
              end
          end
      end
  end.

(******************************************************************************)
(* PROVEN THEOREMS                                                            *)
(******************************************************************************)

(* Constrict preserves num >= 1 when starting with num >= 1 *)
Theorem constrict_preserves_positive : forall num den b syn' b' h,
  constrict (mkSynapse (fs num, den)) b = (syn', b', h) ->
  exists num', conductance syn' = (fs num', den).
Proof.
  intros num den b syn' b' h Hconstr.
  unfold constrict in Hconstr.
  destruct b.
  - inversion Hconstr; subst. exists num. reflexivity.
  - simpl in Hconstr.
    destruct num.
    + inversion Hconstr; subst. exists fz. reflexivity.
    + inversion Hconstr; subst. exists num. reflexivity.
Qed.

(* Erode preserves denominator - by case analysis on result *)
Theorem erode_preserves_den : forall syn b syn' b' h,
  erode syn b = (syn', b', h) ->
  snd (conductance syn') = snd (conductance syn).
Proof.
  intros [[num den]] b syn' b' h Herode.
  unfold erode in Herode.
  destruct b as [|b0]; [inversion Herode; reflexivity|].
  destruct den as [|[|den1]]; [inversion Herode; reflexivity| inversion Herode; reflexivity|].
  (* den = fs (fs den1), need to handle le_fin_b3 *)
  destruct b0 as [|b0'].
  - (* b0 = fz => le_fin_b3 returns BUnknown *)
    simpl in Herode. inversion Herode; reflexivity.
  - (* b0 = fs b0' => le_fin_b3 recurses *)
    simpl in Herode.
    destruct (le_fin_b3 num den1 b0') as [[r br] hr].
    destruct r; inversion Herode; reflexivity.
Qed.

(* Constrict preserves denominator *)
Theorem constrict_preserves_den : forall syn b syn' b' h,
  constrict syn b = (syn', b', h) ->
  snd (conductance syn') = snd (conductance syn).
Proof.
  intros syn b syn' b' h Hconstr.
  unfold constrict in Hconstr.
  destruct b.
  - inversion Hconstr; subst. reflexivity.
  - destruct syn as [[num den]]. simpl in *.
    destruct num.
    + inversion Hconstr; subst. reflexivity.
    + destruct num; inversion Hconstr; subst; reflexivity.
Qed.

(* Update with inactive input is identity *)
Theorem update_inactive_id : forall err syn b syn' b' h,
  update_synapse err fz syn b = (syn', b', h) ->
  syn' = syn /\ h = fz.
Proof.
  intros. unfold update_synapse in H.
  inversion H; subst. split; reflexivity.
Qed.

(* Train loop terminates *)
Theorem train_loop_terminates : forall fuel n b,
  exists n' c b' h, train_loop fuel n b = (n', c, b', h).
Proof.
  intros fuel. induction fuel; intros n b.
  - exists n, fz, b, fz. reflexivity.
  - simpl. destruct b.
    + exists n, fz, fz, fz. reflexivity.
    + destruct (train_and_epoch n (fs b)) as [[[new_n correct] b'] h1].
      destruct (fin_eq_b3 correct (fs (fs (fs (fs fz)))) b') as [[r b''] h2].
      destruct r.
      * exists new_n, correct, b'', (add_heat h1 h2). reflexivity.
      * specialize (IHfuel new_n b'').
        destruct IHfuel as [n' [c [b_f [h_r Hrec]]]].
        exists n', c, b_f, (add_heat h1 (add_heat h2 h_r)).
        rewrite Hrec. reflexivity.
      * specialize (IHfuel new_n b'').
        destruct IHfuel as [n' [c [b_f [h_r Hrec]]]].
        exists n', c, b_f, (add_heat h1 (add_heat h2 h_r)).
        rewrite Hrec. reflexivity.
Qed.

End Void_Perceptron.
