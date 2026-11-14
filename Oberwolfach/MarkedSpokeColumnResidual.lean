module

public import Oberwolfach.MarkedColumnCorrection
public import Oberwolfach.MarkedSpokeResiduals
public import Oberwolfach.AlternatingRectangles

@[expose] public section

/-! After correcting hub columns, each remaining typed spoke vector has
both zero marginals and is supported on its original spoke graph. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}

theorem markedWheelRimLoad_add
    (ψ χ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) :
    markedWheelRimLoad (ψ+χ) e=markedWheelRimLoad ψ e+markedWheelRimLoad χ e := by
  simp only [markedWheelRimLoad,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem markedWheelSpokeLoad_add
    (ψ χ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (v : V) (u : U) :
    markedWheelSpokeLoad (ψ+χ) j v u=markedWheelSpokeLoad ψ j v u+markedWheelSpokeLoad χ j v u := by
  simp only [markedWheelSpokeLoad,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem marked_spoke_column_residual
    (β η : ℝ) (hβ : 0<β) (hη : 0≤η) (hn : 0<Fintype.card V)
    (hcount : ∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (hrow : ∀ j v,(∑ u,markedSpokeResidual ψ j v u)=0)
    (hcol : ∀ u,(∑ v,markedSpokeResidual ψ false v u)=(m:ℝ)*(∑ v,markedSpokeResidual ψ true v u))
    (herr : ∀ j v u,|markedSpokeResidual ψ j v u|≤η) :
    ∃ Ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad Ψ e=0) ∧
      (∀ D,|Ψ D|≤4*η/(β*(Fintype.card V:ℝ)^m)) ∧
      (∀ j,(fun e : V×U=>markedSpokeResidual ψ j e.1 e.2-markedWheelSpokeLoad Ψ j e.1 e.2)∈
        zeroMarginalSpace (if j then Hₖ else H₀)) ∧
      (∀ j,‖fun e : V×U=>markedSpokeResidual ψ j e.1 e.2-markedWheelSpokeLoad Ψ j e.1 e.2‖≤
        (1+4*(m+1)/β)*η) := by
  let B (u : U) := ∑ v,markedSpokeResidual ψ true v u
  have hBsum : ∑ u,B u=0 := by
    unfold B
    rw [Finset.sum_comm]
    simp only [hrow,Finset.sum_const_zero]
  have hB (u : U) : |B u|≤η*Fintype.card V := by
    calc
      _ ≤ ∑ v,|markedSpokeResidual ψ true v u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : V,η := Finset.sum_le_sum (fun v _=>herr true v u)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
  obtain ⟨Ψ,hR,hrows,hcols,hcoeff,hspokes⟩ := marked_column_correction β η hβ hη hn hcount B hBsum hB
  refine ⟨Ψ,hR,hcoeff,?_,?_⟩
  · intro j
    refine ⟨?_,?_,?_⟩
    · intro v u hmiss
      have hm : ¬(if j then Hₖ v u else H₀ v u) := by cases j <;> exact hmiss
      change markedSpokeResidual ψ j v u-markedWheelSpokeLoad Ψ j v u=0
      rw [markedSpokeResidual_outside ψ j v u hm,markedWheelSpokeLoad_outside Ψ j v u hm,sub_self]
    · intro v
      simp only [Finset.sum_sub_distrib,hrow,hrows,sub_self]
    · intro u
      rw [Finset.sum_sub_distrib,hcols]
      cases j
      · simp only [Bool.false_eq_true,ite_false,hcol]
        simp only [B,sub_self]
      · simp only [ite_true,one_mul]
        simp only [B,sub_self]
  · intro j
    have hη' : 0≤(1+4*(m+1)/β)*η := by positivity
    apply (pi_norm_le_iff_of_nonneg hη').mpr
    intro e
    rw [Real.norm_eq_abs]
    have hh := abs_sub_le (markedSpokeResidual ψ j e.1 e.2) 0 (markedWheelSpokeLoad Ψ j e.1 e.2)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    calc
      _ ≤ η+4*(m+1)*η/β := hh.trans (add_le_add (herr j e.1 e.2) (hspokes j e.1 e.2))
      _ = _ := by ring

end Oberwolfach
