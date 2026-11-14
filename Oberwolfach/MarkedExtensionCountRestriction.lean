module

public import Oberwolfach.MarkedPotentialHubStability
public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.CommonMarkedCycleConstraintCounts
public import Oberwolfach.CommonMarkedPathConstraintCounts

@[expose] public section

/-! Explicit inheritance of the three marked extension counts. The common
path count omits the four root spokes; their presence in the smaller graph is
used only when converting a common path to an actual replacement pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem marked_hub_count_restriction
    (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (β d : ℝ) (hbudget : ((m:ℝ)+1)*d≤β*Fintype.card V)
    (hrow0 : ∀ v,(∑ u,if H₀ v u ∧ ¬H₀' v u then (1:ℝ) else 0)≤d)
    (hrowK : ∀ v,(∑ u,if Hₖ v u ∧ ¬Hₖ' v u then (1:ℝ) else 0)≤d)
    (hbase : ∀ C : MarkedCycleTuple tail head ktail khead m π b,
      2*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}:ℝ)) :
    ∀ C : MarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀' Hₖ' C.val u}:ℝ) := by
  intro C
  have hc (H₀ Hₖ : V → U → Prop) :
      Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}=
        (potentialMarkedHubs (fun j=>if j then Hₖ else H₀) C.val).card := by
    apply Fintype.card_of_subtype
    intro u
    simpa only [Bool.false_eq_true,ite_false,ite_true] using
      potentialMarkedHubs_mem (fun j=>if j then Hₖ else H₀) C.val u
  have hdif : ∀ (j : Bool) v,(∑ u,bipAdj (fun v u=>
      ¬((if j then Hₖ v u else H₀ v u)↔(if j then Hₖ' v u else H₀' v u))) v u)≤d := by
    intro j v
    cases j
    · have he (u : U) : ¬(H₀ v u↔H₀' v u) ↔ H₀ v u ∧ ¬H₀' v u := by
        have hh := hH₀ v u;tauto
      simpa only [Bool.false_eq_true,ite_false,bipAdj,he] using hrow0 v
    · have he (u : U) : ¬(Hₖ v u↔Hₖ' v u) ↔ Hₖ v u ∧ ¬Hₖ' v u := by
        have hh := hHₖ v u;tauto
      simpa only [ite_true,bipAdj,he] using hrowK v
  have hloss := potentialMarkedHubs_change (fun j=>if j then Hₖ else H₀)
    (fun j=>if j then Hₖ' else H₀') C.val d (by
      intro j v
      convert hdif j v using 1 <;> simp only [ite_apply] <;> congr!)
  have hb := hbase (markedCycleToLarger PE PK C)
  change 2*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C.val u}:ℝ) at hb
  rw [hc H₀ Hₖ] at hb
  rw [hc H₀' Hₖ']
  have hh := (abs_le.mp hloss).1
  linarith

theorem marked_common_cycle_count_restriction
    (hm : 1≤m) (PE : E → Prop) (PK : K → Prop)
    (β d : ℝ) (hbudget : 3*((m:ℝ)+1)*d≤β*Fintype.card V)
    (hE : ∀ x,(∑ e,if ¬PE e ∧ tail e=x then (1:ℝ) else 0)≤d)
    (hK : ∀ x,(∑ e,if ¬PK e ∧ ktail e=x then (1:ℝ) else 0)≤d)
    (hH0 : ∀ u,(∑ x,if H₀ x u ∧ ¬H₀' x u then (1:ℝ) else 0)≤d)
    (hHK : ∀ u,(∑ x,if Hₖ x u ∧ ¬Hₖ' x u then (1:ℝ) else 0)≤d)
    (u u' : U)
    (hbase : 2*β*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ)) :
    β*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card (CommonMarkedCycle (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' u u'):ℝ) := by
  have hloss := commonMarkedCycle_deletion_count hm tail head ktail khead π b PE PK
    H₀ Hₖ H₀' Hₖ' u u' d hE hK hH0 hHK
  have hscale := mul_le_mul_of_nonneg_right hbudget (pow_nonneg (by positivity : 0≤(Fintype.card V:ℝ)) m)
  have hscale' : 3*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^m≤β*(Fintype.card V:ℝ)^(m+1) := by
    convert hscale using 1 <;> ring
  linarith

theorem marked_replacement_pair_count_restriction
    (hm : 1≤m) (PE : E → Prop) (PK : K → Prop)
    (β d : ℝ) (hbudget : 4*((m:ℝ)+1)*d≤β*Fintype.card V)
    (hEout : ∀ x,(∑ e,if ¬PE e ∧ tail e=x then (1:ℝ) else 0)≤d)
    (hEin : ∀ x,(∑ e,if ¬PE e ∧ head e=x then (1:ℝ) else 0)≤d)
    (hKout : ∀ x,(∑ e,if ¬PK e ∧ ktail e=x then (1:ℝ) else 0)≤d)
    (hKin : ∀ x,(∑ e,if ¬PK e ∧ khead e=x then (1:ℝ) else 0)≤d)
    (hH0 : ∀ u,(∑ x,if H₀ x u ∧ ¬H₀' x u then (1:ℝ) else 0)≤d)
    (hHK : ∀ u,(∑ x,if Hₖ x u ∧ ¬Hₖ' x u then (1:ℝ) else 0)≤d)
    (i : Fin (m+1)) (v v' : V) (u u' : U)
    (hroot : (if markedPositionType i then Hₖ' v u else H₀' v u) ∧
      (if markedPositionType i then Hₖ' v u' else H₀' v u') ∧
      (if markedPositionType i then Hₖ' v' u else H₀' v' u) ∧
      (if markedPositionType i then Hₖ' v' u' else H₀' v' u'))
    (hbase : 2*β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ i v v' u u'):ℝ)) :
    β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (MarkedReplacementPair (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' i v v' u u'):ℝ) := by
  have hloss := commonMarkedPath_deletion_count hm tail head ktail khead π b PE PK
    H₀ Hₖ H₀' Hₖ' i v v' u u' d hEout hEin hKout hKin hH0 hHK
  have hscale := mul_le_mul_of_nonneg_right hbudget (pow_nonneg (by positivity : 0≤(Fintype.card V:ℝ)) (m-1))
  have hscale' : 4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1)≤β*(Fintype.card V:ℝ)^m := by
    have he : (Fintype.card V:ℝ)^m=(Fintype.card V:ℝ)*(Fintype.card V:ℝ)^(m-1) := by
      rw [← pow_succ'];congr 1;omega
    rw [he]
    convert hscale using 1 <;> ring
  have hpath : β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (CanonicalCommonMarkedPath (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' i v v' u u'):ℝ) := by
    linarith
  have hpair := canonicalCommonMarkedPath_card_le
    (tail:=fun e : {e // PE e}=>tail e.val) (head:=fun e=>head e.val)
    (ktail:=fun e : {e // PK e}=>ktail e.val) (khead:=fun e=>khead e.val) (π:=π) (b:=b) hroot
  exact hpath.trans (by
    simp only [← Nat.card_eq_fintype_card] at hpair ⊢
    exact_mod_cast hpair)

end Oberwolfach
