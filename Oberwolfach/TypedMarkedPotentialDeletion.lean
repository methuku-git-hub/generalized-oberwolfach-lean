module

public import Oberwolfach.TypedMarkedPotentialDegreeStability
public import Oberwolfach.ResourceRootOmittedMonotonicity

@[expose] public section

/-! All-root monotone deletion bounds with the supplied coefficients fixed.
The smaller state may be selected after the parent state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}

theorem typedMarkedPotentialLoad_mono
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (hw : ∀ W,0≤w W)
    (R R' : E⊕K → Prop) (H H' : Bool → V → U → Prop)
    (hR : ∀ e,R' e → R e) (hH : ∀ j v u,H' j v u → H j v u)
    (e : (E⊕K)⊕(Bool×V×U)) :
    typedMarkedPotentialLoad w R' H' e≤typedMarkedPotentialLoad w R H e := by
  apply resourceRootOmittedLoad_mono _ w hw
  intro f hf
  cases f with
  | inl f => exact hR f hf
  | inr s => exact hH s.1 s.2.1 s.2.2 hf

theorem typedMarkedPotentialLoad_degree_stability
    (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R R' : E⊕K → Prop) (H H' : Bool → V → U → Prop) (d : ℝ) (hd : 0≤d)
    (hout : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
    (hin : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
    (hHout : ∀ j x,(∑ u,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d)
    (hHin : ∀ j u,(∑ x,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d)
    (e : (E⊕K)⊕(Bool×V×U)) :
    |typedMarkedPotentialLoad w R' H' e-typedMarkedPotentialLoad w R H e|≤
      11*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  cases e with
  | inl e => exact typedMarkedPotentialLoad_rim_degree_stability hm hn hu w B hB hw R R' H H' d hd hout hin hHout hHin e
  | inr s =>
    rcases s with ⟨j,v,u⟩
    apply (typedMarkedPotentialLoad_spoke_degree_stability hm hn w B hB hw R R' H H' d hd hout hin hHout hHin j v u).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    gcongr
    norm_num

theorem typedMarkedPotentialLoad_deletion
    (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R R' : E⊕K → Prop) (H H' : Bool → V → U → Prop) (t : ℝ) (ht : 0≤t)
    (hR : ∀ e,R' e → R e) (hH : ∀ j v u,H' j v u → H j v u)
    (hout : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤t*Fintype.card V)
    (hin : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤t*Fintype.card V)
    (hHout : ∀ j x,(∑ u,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤t*Fintype.card V)
    (hHin : ∀ j u,(∑ x,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤t*Fintype.card V)
    (e : (E⊕K)⊕(Bool×V×U)) :
    0≤typedMarkedPotentialLoad w R H e-typedMarkedPotentialLoad w R' H' e ∧
      typedMarkedPotentialLoad w R H e-typedMarkedPotentialLoad w R' H' e≤11*((m:ℝ)+1)^4*B*t := by
  have hh := typedMarkedPotentialLoad_degree_stability hm hn hu w B hB hw R R' H H'
    (t*Fintype.card V) (mul_nonneg ht (Nat.cast_nonneg _)) hout hin hHout hHin e
  have hnR : (Fintype.card V:ℝ)≠0 := ne_of_gt (by exact_mod_cast hn)
  have heq : 11*((m:ℝ)+1)^4*B*(t*Fintype.card V)/Fintype.card V=11*((m:ℝ)+1)^4*B*t := by field_simp
  rw [heq,abs_sub_comm] at hh
  exact ⟨sub_nonneg.mpr (typedMarkedPotentialLoad_mono w (fun W=>(hw W).1) R R' H H' hR hH e),(le_abs_self _).trans hh⟩

end Oberwolfach
