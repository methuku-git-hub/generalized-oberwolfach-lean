module

public import Oberwolfach.ColourRetentionCoins

@[expose] public section

/-! Colour marginals for arbitrary colour sets, preserving the original
joint law of the colour and its retention coin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_withCoin_colour_event {C : Type*} [Fintype C]
    (μ : FiniteLaw C) (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1) (P : C → Prop) :
    (μ.withCoin a ha).probability (fun x=>P x.1)=μ.probability P := by
  unfold FiniteLaw.probability FiniteLaw.withCoin
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_bool]
  by_cases hc : P c <;> simp only [hc,ite_true,ite_false,Bool.false_eq_true] <;> ring

theorem finiteLaw_probability_mem_finset {C : Type*} [Fintype C]
    (μ : FiniteLaw C) (S : Finset C) :
    μ.probability (fun c=>c∈S)=∑ c∈S,μ.mass c := by
  classical
  unfold FiniteLaw.probability
  calc
    _ = ∑ c,if c∈S then μ.mass c else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c∈S <;> simp [hc]
    _ = _ := by simp

theorem finiteLaw_withCoin_avoid_finset {C : Type*} [Fintype C]
    (μ : FiniteLaw C) (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1) (S : Finset C) :
    (μ.withCoin a ha).probability (fun x=>x.1∉S)=1-∑ c∈S,μ.mass c := by
  calc
    _ = μ.probability (fun c=>c∉S) := finiteLaw_withCoin_colour_event μ a ha (fun c=>c∉S)
    _ = _ := by
      have h := finiteLaw_probability_compl μ (fun c=>c∈S)
      rw [finiteLaw_probability_mem_finset] at h
      linarith

end Oberwolfach
