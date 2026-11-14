module

public import Oberwolfach.FiniteUniform

@[expose] public section

/-! Composition of finite pushforward laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_map_map {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ]
    (μ : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → Δ) :
    (μ.map f).map g = μ.map (fun ω => g (f ω)) := by
  apply finiteLaw_ext
  intro δ
  unfold FiniteLaw.map
  have hh (γ : Γ) : (if g γ = δ then ∑ ω, if f ω = γ then μ.mass ω else 0 else 0) =
      ∑ ω, if f ω = γ then (if g (f ω) = δ then μ.mass ω else 0) else 0 := by
    by_cases h : g γ = δ
    · simp only [h, ite_true]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hf : f ω = γ <;> simp [hf, h]
    · simp only [h, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro ω _
      by_cases hf : f ω = γ <;> simp [hf, h]
  simp_rw [hh]
  rw [Finset.sum_comm]
  simp

end Oberwolfach
