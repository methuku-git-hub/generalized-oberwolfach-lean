module

public import Oberwolfach.MarkedHostBalance

@[expose] public section

/-! Exact rim loads force zero spoke-residual row sums; the hub degree
identity gives the marked-to-ordinary column ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedSpokeResidual {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (v : V) (u : U) : ℝ :=
  (if (if j then Hₖ v u else H₀ v u) then 1 else 0)-markedWheelSpokeLoad ψ j v u

theorem markedSpokeResidual_outside {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (v : V) (u : U)
    (hm : ¬(if j then Hₖ v u else H₀ v u)) : markedSpokeResidual ψ j v u=0 := by
  rw [markedSpokeResidual,if_neg hm,markedWheelSpokeLoad_outside ψ j v u hm,sub_self]

theorem markedSpokeResidual_zero_rows {V U E K : Type*} [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (hK : ∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0)
    (hout : ∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (hR : ∀ e,markedWheelRimLoad ψ e=1) (j : Bool) (v : V) :
    (∑ u,markedSpokeResidual ψ j v u)=0 := by
  have hmark := markedWheelRimLoad_marked_head hkinj ψ v
  have hall := markedWheelRimLoad_outgoing hinj hkinj ψ v
  have he : markedWheelRimLoad ψ=(fun _ => (1:ℝ)) := funext hR
  rw [he,occurrenceSumLinear_one,hK] at hmark
  rw [he,occurrenceSumLinear_one,hout] at hall
  cases j
  · simp only [markedSpokeResidual,Bool.false_eq_true,ite_false,Finset.sum_sub_distrib]
    linarith
  · simp only [markedSpokeResidual,ite_true,Finset.sum_sub_distrib]
    linarith

theorem markedSpokeResidual_column_ratio {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (hhub : ∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(m:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (u : U) :
    (∑ v,markedSpokeResidual ψ false v u)=(m:ℝ)*(∑ v,markedSpokeResidual ψ true v u) := by
  simp only [markedSpokeResidual,Bool.false_eq_true,ite_false,ite_true,Finset.sum_sub_distrib]
  rw [hhub,markedWheelSpokeLoad_column_ratio]
  ring

end Oberwolfach
