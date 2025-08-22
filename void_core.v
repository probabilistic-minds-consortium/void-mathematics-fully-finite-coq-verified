(******************************************************************************)
(* void_core.v - The Foundation of Void Pascal                               *)
(* Native saturation, 3-valued truth, everything costs                       *)
(* NO PEANO. NO NAT. NO HIDDEN INFINITIES.                                   *)
(******************************************************************************)

(******************************************************************************)
(* THE RESOURCE OBJECT 𝔽                                                     *)
(******************************************************************************)

Inductive F : Type :=
  | O : F        (* Quiescent - the zero state *)
  | S : F -> F   (* Advance - ability to step forward *)
  | Omega : F.   (* Exhaustion - the absorbing ceiling *)

(* Aliases for clarity *)
Definition Budget := F.
Definition Heat := F.

(* Predecessor - partial and absorbing *)
Definition p (x : F) : F :=
  match x with
  | O => O        (* p(0) = 0 *)
  | S x' => x'    (* Step back *)
  | Omega => Omega (* p(Ω) = Ω *)
  end.

(* Successor with saturation *)
Definition s (x : F) : F :=
  match x with
  | Omega => Omega  (* s(Ω) = Ω - NATIVE SATURATION *)
  | _ => S x
  end.

(* Composition - sequential execution *)
Definition compose (f g : F -> F) (x : F) : F :=
  f (g x).

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

(******************************************************************************)
(* THREE-VALUED LOGIC                                                        *)
(******************************************************************************)

Inductive Bool3 : Type :=
  | BTrue : Bool3
  | BFalse : Bool3  
  | BUnknown : Bool3.

(* Collapse for UI edges only - MUST BE LOGGED *)
Definition collapse3 (b : Bool3) : bool :=
  match b with
  | BTrue => true
  | _ => false  (* Unknown collapses to false *)
  end.

(******************************************************************************)
(* HEAT ARITHMETIC                                                           *)
(******************************************************************************)

(* Heat addition - saturating *)
Fixpoint add_heat (h1 h2 : F) : F :=
  match h2 with
  | O => h1
  | S h2' => 
      match h1 with
      | Omega => Omega
      | _ => S (add_heat h1 h2')
      end
  | Omega => Omega
  end.

(******************************************************************************)
(* SPENDING PRIMITIVE                                                        *)
(******************************************************************************)

(* Helper: check if we can afford a cost *)
Fixpoint check_afford (cost budget : F) : (Bool3 * Budget) :=
  match cost, budget with
  | O, b => (BTrue, b)
  | _, O => (BFalse, O)  (* Can't afford *)
  | _, Omega => (BTrue, Omega)  (* Omega affords anything *)
  | S c', S b' => check_afford c' b'
  | Omega, S _ => (BFalse, O)  (* Can't afford Omega cost *)
  end.

(* Spend always emits heat = cost, even on failure *)
Definition spend (cost : F) (budget : F) : (Bool3 * Budget * Heat) :=
  match cost with
  | O => (BTrue, budget, O)  (* Zero cost always succeeds *)
  | _ =>
      match check_afford cost budget with
      | (BTrue, remaining) => (BTrue, remaining, cost)
      | (BFalse, _) => (BFalse, O, cost)  (* HEAT EMITTED EVEN ON FAILURE *)
      | (BUnknown, remaining) => (BUnknown, remaining, cost)
      end
  end.

(******************************************************************************)
(* THREE-VALUED COMPARISONS - Need these before arithmetic                   *)
(******************************************************************************)

(* Equality check eq3 *)
Fixpoint eq3 (x y : F) (budget : Budget) : (Bool3 * Budget * Heat) :=
  match budget with
  | O => (BUnknown, O, O)  (* No budget - Unknown *)
  | S b' =>
      match x, y with
      | O, O => (BTrue, b', S O)
      | Omega, Omega => (BTrue, b', S O)
      | S x', S y' =>
          let result := eq3 x' y' b' in
          match result with
          | (r, b'', h) => (r, b'', S h)
          end
      | _, _ => (BFalse, b', S O)
      end
  | Omega =>
      (* Omega budget - but still costs *)
      match x, y with
      | O, O => (BTrue, Omega, S O)
      | Omega, Omega => (BTrue, Omega, S O)
      | S x', S y' => eq3 x' y' Omega
      | _, _ => (BFalse, Omega, S O)
      end
  end.

(* Less-or-equal check le3 *)
Fixpoint le3 (x y : F) (budget : Budget) : (Bool3 * Budget * Heat) :=
  match budget with
  | O => (BUnknown, O, O)
  | S b' =>
      match x, y with
      | O, _ => (BTrue, b', S O)
      | _, O => (BFalse, b', S O)
      | Omega, _ => (BTrue, b', S O)  (* Omega ≤ anything *)
      | _, Omega => (BTrue, b', S O)   (* anything ≤ Omega *)
      | S x', S y' =>
          let result := le3 x' y' b' in
          match result with
          | (r, b'', h) => (r, b'', S h)
          end
      end
  | Omega =>
      match x, y with
      | O, _ => (BTrue, Omega, S O)
      | _, O => (BFalse, Omega, S O)
      | Omega, _ => (BTrue, Omega, S O)
      | _, Omega => (BTrue, Omega, S O)
      | S x', S y' => le3 x' y' Omega
      end
  end.

(******************************************************************************)
(* SATURATING ARITHMETIC                                                     *)
(******************************************************************************)

(* Addition with saturation ⊕ *)
Fixpoint add_sat (x y : F) (budget : Budget) : (F * Budget * Heat) :=
  match budget with
  | O => (x, O, O)  (* No budget - return x unchanged *)
  | _ =>
      match y with
      | O => (x, budget, O)  (* Adding zero costs nothing *)
      | S y' =>
          match x with
          | Omega => (Omega, budget, S O)  (* Already saturated *)
          | _ =>
              match add_sat (s x) y' (p budget) with
              | (z, b', h) => (z, b', S h)
              end
          end
      | Omega => (Omega, budget, S O)  (* Jump straight to Omega *)
      end
  end.

Notation "x ⊕ y" := (add_sat x y) (at level 50, left associativity).

(* Subtraction with floor at O ⊖ *)
Fixpoint sub_floor (x y : F) (budget : Budget) : (F * Budget * Heat) :=
  match budget with
  | O => (x, O, O)
  | _ =>
      match y with
      | O => (x, budget, O)
      | S y' =>
          match x with
          | O => (O, budget, S O)  (* Floor at zero *)
          | _ =>
              match sub_floor (p x) y' (p budget) with
              | (z, b', h) => (z, b', S h)
              end
          end
      | Omega =>
          match x with
          | Omega => (O, budget, S O)  (* Omega - Omega = O *)
          | _ => (O, budget, S O)      (* Can't subtract Omega from finite *)
          end
      end
  end.

Notation "x ⊖ y" := (sub_floor x y) (at level 50, left associativity).

(* Multiplication via repeated addition ⊗ *)
Fixpoint mul_sat (x y : F) (budget : Budget) : (F * Budget * Heat) :=
  match budget with
  | O => (O, O, O)
  | _ =>
      match y with
      | O => (O, budget, O)
      | S y' =>
          match mul_sat x y' (p budget) with
          | (prod, b1, h1) =>
              match add_sat prod x b1 with
              | (result, b2, h2) => (result, b2, add_heat h1 h2)
              end
          end
      | Omega =>
          match x with
          | O => (O, budget, S O)
          | _ => (Omega, budget, S O)  (* Anything × Omega = Omega *)
          end
      end
  end.

Notation "x ⊗ y" := (mul_sat x y) (at level 40, left associativity).

(******************************************************************************)
(* DIVISION WITH FUEL                                                        *)
(******************************************************************************)

(* Division step helper *)
Fixpoint div_step (dividend divisor quotient remainder fuel : F) (budget : Budget) 
  : (F * F * Bool3 * Budget * Heat) :=
  match fuel with
  | O => (quotient, remainder, BUnknown, budget, O)  (* Fuel exhausted *)
  | S fuel' =>
      match le3 divisor remainder budget with  (* Can we subtract? *)
      | (BTrue, b1, h1) =>
          match sub_floor remainder divisor b1 with
          | (r', b2, h2) =>
              match add_sat quotient (S O) b2 with
              | (q', b3, h3) =>
                  match div_step dividend divisor q' r' fuel' b3 with
                  | (q_final, r_final, exact, b4, h4) =>
                      (q_final, r_final, exact, b4, 
                       add_heat h1 (add_heat h2 (add_heat h3 h4)))
                  end
              end
          end
      | (BFalse, b1, h1) => (quotient, remainder, BTrue, b1, h1)  (* Exact result *)
      | (BUnknown, b1, h1) => (quotient, remainder, BUnknown, b1, h1)
      end
  | Omega => (quotient, remainder, BTrue, budget, O)  (* Omega fuel = complete *)
  end.

Definition div_fuel (x y : F) (fuel : F) (budget : Budget) 
  : (F * F * Bool3 * Budget * Heat) :=
  match fuel, budget with
  | O, _ => (O, x, BUnknown, budget, O)  (* Out of fuel - Unknown *)
  | _, O => (O, x, BUnknown, O, O)       (* Out of budget - Unknown *)
  | _, _ =>
      match y with
      | O => (O, x, BFalse, budget, S O)  (* Division by zero *)
      | _ => div_step x y O x fuel budget
      end
  end.

(******************************************************************************)
(* MIN/MAX WITH UNCERTAINTY                                                  *)
(******************************************************************************)

(* Decisional min - returns winner and proof quality *)
Definition min_dec (x y : F) (budget : Budget) 
  : (F * Bool3 * Budget * Heat) :=
  match le3 x y budget with
  | (BTrue, b', h) => (x, BTrue, b', h)
  | (BFalse, b', h) => (y, BFalse, b', h)
  | (BUnknown, b', h) => (x, BUnknown, b', h)  (* Default to x on Unknown *)
  end.

(* Interval min - can return Range when uncertain *)
Inductive FInterval :=
  | Exact : F -> FInterval
  | Range : F -> F -> FInterval.

Definition min_interval (x y : F) (budget : Budget) 
  : (FInterval * Budget * Heat) :=
  match le3 x y budget with
  | (BTrue, b', h) => (Exact x, b', h)
  | (BFalse, b', h) => (Exact y, b', h)
  | (BUnknown, b', h) => (Range x y, b', h)  (* Can't decide - return both *)
  end.

(* Max versions - dual *)
Definition max_dec (x y : F) (budget : Budget) 
  : (F * Bool3 * Budget * Heat) :=
  match le3 x y budget with
  | (BTrue, b', h) => (y, BTrue, b', h)
  | (BFalse, b', h) => (x, BFalse, b', h)
  | (BUnknown, b', h) => (y, BUnknown, b', h)
  end.

Definition max_interval (x y : F) (budget : Budget) 
  : (FInterval * Budget * Heat) :=
  match le3 x y budget with
  | (BTrue, b', h) => (Exact y, b', h)
  | (BFalse, b', h) => (Exact x, b', h)
  | (BUnknown, b', h) => (Range x y, b', h)
  end.

(******************************************************************************)
(* CORE AXIOMS AND INVARIANTS                                                *)
(******************************************************************************)

(* Saturation axioms *)
Axiom s_omega_absorbing : s Omega = Omega.
Axiom p_zero_absorbing : p O = O.
Axiom p_omega_absorbing : p Omega = Omega.

(* Heat conservation *)
Axiom heat_conservation : forall (op : F -> F -> Budget -> (F * Budget * Heat)) x y b b' result h,
  op x y b = (result, b', h) -> 
  exists b_consumed, add_heat b_consumed h = b /\ 
                     add_heat b' b_consumed = b.

(* Composition properties *)
Axiom compose_assoc : forall f g h x,
  (f ∘ (g ∘ h)) x = ((f ∘ g) ∘ h) x.

Axiom compose_id : forall f x,
  (f ∘ (fun y => y)) x = f x /\
  ((fun y => y) ∘ f) x = f x.

Axiom omega_absorbing_compose : forall f,
  f Omega = Omega -> forall g, (f ∘ g) Omega = Omega.

(******************************************************************************)
(* OBSERVATIONAL EQUALITY                                                    *)
(******************************************************************************)

Definition obs_equal (x y : F) : Prop :=
  forall (test : F -> Budget -> (Bool3 * Budget * Heat)) (b : Budget),
    test x b = test y b.

Notation "x ≈ y" := (obs_equal x y) (at level 70).

(******************************************************************************)
(* NO CONVERSIONS TO NAT/Z/REAL - THIS IS THE LAW                           *)
(******************************************************************************)

(* We explicitly DO NOT provide:
   - F_to_nat
   - F_to_Z  
   - F_to_R
   - nat_to_F
   
   The only way in is through construction with budget.
   The only way out is through observation with budget.
*)