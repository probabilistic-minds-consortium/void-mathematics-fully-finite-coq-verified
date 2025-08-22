(******************************************************************************)
(* void_metaprobability.v - PROBABILITY OF PROBABILITY                        *)
(* When you're uncertain about your uncertainty                               *)
(* Higher-order confidence costs exponentially more to maintain               *)
(******************************************************************************)

Require Import void_finite_minimal.
Require Import void_probability_minimal.
Require Import void_arithmetic.
Require Import Coq.Lists.List.
Import ListNotations.

Module Void_Metaprobability.

Import Void_Probability_Minimal.
Import Void_Arithmetic.

(******************************************************************************)
(* HELPER DEFINITIONS - Missing probability operations                        *)
(******************************************************************************)

(* Multiply probabilities with budget *)
Definition mult_prob_b (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin n1 n2 b with
  | (new_n, b1) =>
      match mult_fin d1 d2 b1 with
      | (new_d, b2) => ((new_n, new_d), b2)
      end
  end.

(* Difference between probabilities with budget *)
Definition prob_diff_with_budget (p1 p2 : FinProb) (b : Budget) : (FinProb * Budget) :=
  let (n1, d1) := p1 in
  let (n2, d2) := p2 in
  match mult_fin n1 d2 b with
  | (v1, b1) =>
      match mult_fin n2 d1 b1 with
      | (v2, b2) =>
          match mult_fin d1 d2 b2 with
          | (common_d, b3) =>
              match le_fin_b v1 v2 b3 with
              | (true, b4) => 
                  match sub_fin v2 v1 b4 with
                  | (diff_n, b5) => ((diff_n, common_d), b5)
                  end
              | (false, b4) =>
                  match sub_fin v1 v2 b4 with
                  | (diff_n, b5) => ((diff_n, common_d), b5)
                  end
              end
          end
      end
  end.

(* Boolean helpers *)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Pipe operator helper for cleaner code *)
Notation "x |> f" := (f x) (at level 70, only parsing).

(******************************************************************************)
(* METAPROBABILITY - Uncertainty about uncertainty                           *)
(******************************************************************************)

Inductive MetaProb :=
  | Sharp : FinProb -> MetaProb
    (* "I know exactly" - maximum confidence, maximum cost *)
  | Fuzzy : FinProb -> FinProb -> FinProb -> MetaProb  
    (* (lower, center, upper) bounds with decreasing confidence *)
  | Vague : FinProb -> FinProb -> MetaProb
    (* "Somewhere between these" - cheaper than Fuzzy *)
  | Exhausted : MetaProb
    (* "I have no idea" - free but useless *)
  | Void : MetaProb
    (* Complete uncertainty - not even bounds *).

(******************************************************************************)
(* COST OF CONFIDENCE                                                        *)
(******************************************************************************)

(* Maintaining confidence levels costs budget *)
Definition confidence_cost (mp : MetaProb) : Fin :=
  match mp with
  | Sharp _ => fs (fs (fs (fs fz)))      (* 4 - very expensive *)
  | Fuzzy _ _ _ => fs (fs (fs fz))       (* 3 - expensive *)
  | Vague _ _ => fs (fs fz)              (* 2 - moderate *)
  | Exhausted => fs fz                   (* 1 - cheap *)
  | Void => fz                           (* 0 - free *)
  end.

(* Can we afford this confidence level? *)
Definition can_afford_confidence (mp : MetaProb) (b : Budget) : bool :=
  match le_fin_b (confidence_cost mp) b b with
  | (can_afford, _) => can_afford
  end.

(******************************************************************************)
(* CONFIDENCE DECAY - Without maintenance, confidence degrades               *)
(******************************************************************************)

Definition decay_confidence (mp : MetaProb) : MetaProb :=
  match mp with
  | Sharp p => Fuzzy p p p  (* Sharp becomes fuzzy *)
  | Fuzzy l c u => 
      (* Bounds spread *)
      let l' := match l with
                | (fs n, d) => (n, d)  (* Lower bound decreases *)
                | _ => l
                end in
      let u' := match u with
                | (n, fs (fs d)) => (n, fs (fs (fs d)))  (* Upper increases *)
                | _ => u
                end in
      Vague l' u'
  | Vague l u => Exhausted  (* Vague becomes exhausted *)
  | Exhausted => Void       (* Exhausted becomes void *)
  | Void => Void            (* Void is stable *)
  end.

(* Decay with budget tracking *)
Definition decay_confidence_b (mp : MetaProb) (b : Budget) 
  : (MetaProb * Budget) :=
  match b with
  | fz => (decay_confidence mp, fz)  (* Forced decay *)
  | fs b' =>
      match can_afford_confidence mp b with
      | true => (mp, b')  (* Can maintain *)
      | false => (decay_confidence mp, b')  (* Must decay *)
      end
  end.

(******************************************************************************)
(* METAPROBABILITY ARITHMETIC                                                *)
(******************************************************************************)

(* Adding metaprobabilities - confidence degrades *)
Definition add_metaprob_b (mp1 mp2 : MetaProb) (b : Budget) 
  : (MetaProb * Budget) :=
  match mp1, mp2, b with
  | Void, _, _ => (Void, b)
  | _, Void, _ => (Void, b)
  | Exhausted, _, _ => (Exhausted, b)
  | _, Exhausted, _ => (Exhausted, b)
  | _, _, fz => (Exhausted, fz)
  
  | Sharp p1, Sharp p2, fs b' =>
      (* Adding sharp probabilities - expensive *)
      match add_prob_b p1 p2 b' with
      | (sum, b'') =>
          match le_fin_b (fs (fs (fs fz))) b'' b'' with
          | (true, b''') => (Sharp sum, b''')
          | (false, b''') => (Fuzzy sum sum sum, b''')  (* Can't afford sharp *)
          end
      end
      
  | Sharp p, Fuzzy l c u, fs b' 
  | Fuzzy l c u, Sharp p, fs b' =>
      (* Mixed precision - result is fuzzy *)
      match add_prob_b p l b' with
      | (new_l, b1) =>
          match add_prob_b p c b1 with
          | (new_c, b2) =>
              match add_prob_b p u b2 with
              | (new_u, b3) => (Fuzzy new_l new_c new_u, b3)
              end
          end
      end
      
  | Fuzzy l1 c1 u1, Fuzzy l2 c2 u2, fs b' =>
      (* Fuzzy addition - bounds spread *)
      match add_prob_b l1 l2 b' with
      | (new_l, b1) =>
          match add_prob_b c1 c2 b1 with
          | (new_c, b2) =>
              match add_prob_b u1 u2 b2 with
              | (new_u, b3) => (Fuzzy new_l new_c new_u, b3)
              end
          end
      end
      
  | Vague l1 u1, Vague l2 u2, fs b' =>
      (* Vague addition - even vaguer *)
      match add_prob_b l1 l2 b' with
      | (new_l, b1) =>
          match add_prob_b u1 u2 b1 with
          | (new_u, b2) => (Vague new_l new_u, b2)
          end
      end
      
  | _, _, fs b' => (Exhausted, b')  (* Other combinations exhaust *)
  end.

(******************************************************************************)
(* BAYESIAN UPDATE WITH CONFIDENCE DEGRADATION                               *)
(******************************************************************************)

(* Update degrades confidence based on available energy *)
Definition tired_update_b (prior : MetaProb) (evidence : FinProb) (b : Budget)
  : (MetaProb * Budget) :=
  match b with
  | fz => (Exhausted, fz)  (* No energy - no update *)
  | fs fz => 
      (* Minimal energy - just decay confidence *)
      (decay_confidence prior, fs fz)
  | fs (fs b') =>
      (* Some energy - attempt update with degradation based on energy level *)
      match b' with
      | fz | fs fz | fs (fs fz) =>
          (* Low energy (2-4 units) - blurry update *)
          match prior with
          | Sharp p =>
              match mult_prob_b p evidence (fs (fs b')) with
              | (updated, b'') =>
                  (* Can't maintain sharpness after update *)
                  (Fuzzy updated updated updated, b'')
              end
          | Fuzzy l c u =>
              match mult_prob_b c evidence (fs (fs b')) with
              | (new_c, b'') =>
                  (* Bounds spread during update *)
                  (Vague l u, b'')
              end
          | _ => (prior, fs (fs b'))  (* Too vague to update *)
          end
      | _ =>
          (* Higher energy (5+ units) - proper Bayesian update *)
          match prior with
          | Sharp p =>
              match mult_prob_b p evidence (fs (fs b')) with
              | (updated, b'') => (Sharp updated, b'')
              end
          | Fuzzy l c u =>
              match mult_prob_b l evidence (fs (fs b')) with
              | (new_l, b1) =>
                  match mult_prob_b c evidence b1 with
                  | (new_c, b2) =>
                      match mult_prob_b u evidence b2 with
                      | (new_u, b3) => (Fuzzy new_l new_c new_u, b3)
                      end
                  end
              end
          | _ => (prior, fs (fs b'))
          end
      end
  end.

(******************************************************************************)
(* CONFIDENCE COMPOSITION - Second-order uncertainty                         *)
(******************************************************************************)

(* Confidence about confidence *)
Inductive MetaMetaProb :=
  | Certain : MetaProb -> MetaMetaProb
    (* "I'm sure about my uncertainty" *)
  | Doubtful : MetaProb -> MetaProb -> MetaMetaProb
    (* "My confidence is somewhere between these" *)
  | Confused : MetaMetaProb
    (* "I don't even know how uncertain I am" *).

(* This costs even more! *)
Definition metameta_cost (mmp : MetaMetaProb) : Fin :=
  match mmp with
  | Certain mp => fs (confidence_cost mp)  (* Extra cost on top *)
  | Doubtful mp1 mp2 => 
      fst (add_fin (confidence_cost mp1) (confidence_cost mp2) initial_budget)
  | Confused => fs fz  (* Confusion is cheap *)
  end.

(******************************************************************************)
(* PROBABILITY COLLAPSE UNDER OBSERVATION                                    *)
(******************************************************************************)

(* Observing forces metaprobability to collapse *)
Definition observe_metaprob_b (mp : MetaProb) (observer_energy : Budget)
  : (FinProb * Budget) :=
  match mp, observer_energy with
  | Void, _ => (half, observer_energy)  (* Void collapses to maximum uncertainty *)
  | Exhausted, _ => (half, observer_energy)
  | _, fz => (half, fz)  (* No energy - default to half *)
  
  | Sharp p, fs b' => (p, b')  (* Sharp is already collapsed *)
  
  | Fuzzy l c u, fs b' =>
      (* Collapse to center, costs budget *)
      (c, b')
      
  | Vague l u, fs b' =>
      (* Collapse to midpoint *)
      match add_prob_b l u b' with
      | (sum, b'') =>
          (* Divide by 2 - simplified *)
          ((fst sum, fs (snd sum)), b'')
      end
  end.

(******************************************************************************)
(* CONFIDENCE FIELDS - Spatial distribution of uncertainty                   *)
(******************************************************************************)

(* Different regions have different confidence costs *)
Definition confidence_field (location : Fin) : MetaProb -> Fin :=
  fun mp =>
    match location with
    | fz => confidence_cost mp  (* Origin - normal cost *)
    | fs fz => fs (confidence_cost mp)  (* Away from origin - higher cost *)
    | _ => fs (fs (confidence_cost mp))  (* Far away - very expensive *)
    end.

(* Navigate toward affordable confidence *)
Fixpoint seek_affordable_confidence_aux (mp : MetaProb) (b : Budget) (fuel : Fin) : MetaProb :=
  match fuel with
  | fz => Void
  | fs fuel' =>
      if can_afford_confidence mp b then mp
      else seek_affordable_confidence_aux (decay_confidence mp) b fuel'
  end.

Definition seek_affordable_confidence (mp : MetaProb) (b : Budget) : MetaProb :=
  let cost := confidence_cost mp in
  match le_fin_b cost b b with
  | (true, _) => mp  (* Can afford current confidence *)
  | (false, _) =>
      (* Decay until affordable *)
      seek_affordable_confidence_aux mp b (fs (fs (fs fz)))  (* Try 3 times *)
  end.

(******************************************************************************)
(* PROBABILITY RANGES - Expressing uncertainty through intervals              *)
(******************************************************************************)

(* Range with confidence about its bounds *)
Inductive ProbRange :=
  | Exact : FinProb -> ProbRange
    (* Single point - maximum cost *)
  | Interval : FinProb -> FinProb -> FinProb -> ProbRange  
    (* (min, likely, max) with confidence measure *)
  | Band : FinProb -> FinProb -> Fin -> ProbRange
    (* (center, width, confidence_level) - cheaper than Interval *)
  | Spread : FinProb -> ProbRange
    (* Just a center point with unknown spread *)
  | Unknown : ProbRange
    (* Complete uncertainty about range *).

(* Range precision costs budget to maintain *)
Definition range_precision_cost (pr : ProbRange) : Fin :=
  match pr with
  | Exact _ => fs (fs (fs (fs (fs fz))))     (* 5 - very expensive *)
  | Interval _ _ _ => fs (fs (fs fz))        (* 3 - expensive *)
  | Band _ _ conf => conf                    (* Cost = confidence level *)
  | Spread _ => fs fz                        (* 1 - cheap *)
  | Unknown => fz                            (* 0 - free *)
  end.

(* Range operations that propagate uncertainty *)
Definition combine_ranges_b (r1 r2 : ProbRange) 
                           (op : FinProb -> FinProb -> Budget -> (FinProb * Budget)) 
                           (b : Budget) 
  : (ProbRange * Budget) :=
  match r1, r2, b with
  | Unknown, _, _ => (Unknown, b)
  | _, Unknown, _ => (Unknown, b)
  | _, _, fz => (Unknown, fz)  (* No budget - maximum uncertainty *)
  
  | Exact p1, Exact p2, fs b' =>
      match op p1 p2 b' with
      | (result, b'') =>
          (* Can we maintain exactness? *)
          match le_fin_b (fs (fs (fs (fs fz)))) b'' b'' with
          | (true, b''') => (Exact result, b''')
          | (false, b''') => 
              (* Degrade to interval *)
              (Interval result result result, b''')
          end
      end
      
  | Interval min1 likely1 max1, Interval min2 likely2 max2, fs b' =>
      (* Intervals combine with spreading bounds *)
      match op min1 min2 b' with
      | (new_min, b1) =>
          match op likely1 likely2 b1 with
          | (new_likely, b2) =>
              match op max1 max2 b2 with
              | (new_max, b3) =>
                  (* Widen the interval slightly - uncertainty grows *)
                  let widened_min := match new_min with
                                    | (fs n, d) => 
                                        match n with
                                        | fz => new_min
                                        | _ => (n, d)
                                        end
                                    | _ => new_min
                                    end in
                  let widened_max := match new_max with
                                    | (n, fs (fs d)) => (n, fs (fs (fs d)))
                                    | _ => new_max
                                    end in
                  (Interval widened_min new_likely widened_max, b3)
              end
          end
      end
      
  | Band center1 width1 conf1, Band center2 width2 conf2, fs b' =>
      match op center1 center2 b' with
      | (new_center, b1) =>
          match add_prob_b width1 width2 b1 with
          | (combined_width, b2) =>
              (* Confidence is minimum of the two *)
              match min_fin_b conf1 conf2 b2 with
              | (new_conf, b3) =>
                  (Band new_center combined_width new_conf, b3)
              end
          end
      end
      
  | _, _, fs b' => 
      (* Mixed precision - degrade to unknown *)
      (Unknown, b')
  end.

(* Range containment check - costs budget *)
Definition in_range_b (p : FinProb) (r : ProbRange) (b : Budget) 
  : (FinProb * Budget) :=  (* Returns confidence probability *)
  match r, b with
  | Unknown, _ => (half, b)  (* Maximum uncertainty *)
  | _, fz => (half, fz)
  
  | Exact p', fs b' =>
      match prob_eq_b p p' b' with
      | (true, b'') => ((fs (fs (fs fz)), fs (fs (fs (fs fz)))), b'')  (* 3/4 - high confidence *)
      | (false, b'') => ((fs fz, fs (fs (fs (fs fz)))), b'')  (* 1/4 - low confidence *)
      end
      
  | Interval min likely max, fs b' =>
      (* Check if p is in [min, max] *)
      match le_fin_b (fst min) (fst p) b' with
      | (above_min, b1) =>
          match le_fin_b (fst p) (fst max) b1 with
          | (below_max, b2) =>
              if andb above_min below_max then
                (* In range - check distance from likely *)
                match prob_diff_with_budget p likely b2 with
                | (dist, b3) =>
                    (* Confidence inversely proportional to distance *)
                    match fst dist with
                    | fz => ((fs (fs (fs fz)), fs (fs (fs (fs fz)))), b3)  (* Very confident *)
                    | fs fz => ((fs (fs fz), fs (fs (fs fz))), b3)  (* Confident *)
                    | _ => ((fs fz, fs (fs fz)), b3)  (* Less confident *)
                    end
                end
              else
                ((fs fz, fs (fs (fs (fs (fs fz))))), b2)  (* 1/5 - out of range *)
          end
      end
      
  | Band center width _, fs b' =>
      (* Distance from center determines confidence *)
      match prob_diff_with_budget p center b' with
      | (dist, b1) =>
          match le_fin_b (fst dist) (fst width) b1 with
          | (true, b2) => ((fs (fs fz), fs (fs (fs fz))), b2)  (* 2/3 - in band *)
          | (false, b2) => ((fs fz, fs (fs (fs fz))), b2)  (* 1/3 - outside *)
          end
      end
      
  | Spread center, fs b' =>
      (* Very uncertain containment *)
      (half, b')
  end.

(* Range evolution - ranges naturally spread without maintenance *)
Fixpoint evolve_range_b (r : ProbRange) (time_steps : Fin) (b : Budget) 
  : (ProbRange * Budget) :=
  match time_steps, b with
  | fz, _ => (r, b)
  | _, fz => (Unknown, fz)  (* No budget - complete uncertainty *)
  | fs steps', fs b' =>
      match r with
      | Exact p =>
          (* Exact becomes interval *)
          evolve_range_b (Interval p p p) steps' b'
      | Interval min likely max =>
          (* Bounds spread *)
          let spread_min := match min with
                           | (fs n, d) => 
                               match n with
                               | fz => min
                               | _ => (n, d)
                               end
                           | _ => min
                           end in
          let spread_max := match max with
                           | (n, fs d) => 
                               match d with
                               | fz => max
                               | _ => (n, fs (fs d))
                               end
                           | _ => max
                           end in
          evolve_range_b (Interval spread_min likely spread_max) steps' b'
      | Band center width conf =>
          (* Width increases, confidence decreases *)
          let new_width := match width with
                          | (n, fs d) => (fs n, fs d)
                          | _ => width
                          end in
          let new_conf := match conf with
                         | fs n => n
                         | fz => fz
                         end in
          evolve_range_b (Band center new_width new_conf) steps' b'
      | Spread _ => (Unknown, b')  (* Spread becomes unknown *)
      | Unknown => (Unknown, b')
      end
  end.

(******************************************************************************)
(* PHILOSOPHICAL IMPLICATIONS                                                *)
(******************************************************************************)

(* The system naturally models: 
   
   1. CONFIDENCE EXHAUSTION - Being certain is exhausting. Uncertainty is rest.
   
   2. KNOWLEDGE DECAY - Without active maintenance, all knowledge becomes vague.
   
   3. OBSERVATION COLLAPSE - Looking forces quantum-like collapse of confidence.
   
   4. SPATIAL CONFIDENCE - Some regions of thought-space are more expensive.
   
   5. META-REGRESS - You can be uncertain about your uncertainty about your 
      uncertainty... but each level costs exponentially more.
   
   6. RANGE UNCERTAINTY - Even describing the bounds of your uncertainty
      costs energy, and those bounds naturally spread without maintenance.
   
   This captures how actual bounded agents reason:
   - Start confident (expensive)
   - Gradually become uncertain (sustainable)  
   - Eventually exhausted (free but useless)
   - Finally void (don't even have bounds)
   
   "I don't know" is the thermodynamic ground state of epistemology. *)

(******************************************************************************)
(* EXPORTS                                                                    *)
(******************************************************************************)

Definition MetaProb_ext := MetaProb.
Definition ProbRange_ext := ProbRange.
Definition tired_update_b_ext := tired_update_b.
Definition confidence_cost_ext := confidence_cost.
Definition observe_metaprob_b_ext := observe_metaprob_b.
Definition combine_ranges_b_ext := combine_ranges_b.
Definition in_range_b_ext := in_range_b.

End Void_Metaprobability.