module

public import Oberwolfach.FiniteUniform

@[expose] public section

/-! A constant-size fibre identifies the pushforward of a uniform finite law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_eq_uniform_of_mass_constant
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (μ : FiniteLaw Ω)
    (hc : ∀ x y, μ.mass x = μ.mass y) : μ = FiniteLaw.uniform Ω := by
  apply finiteLaw_ext
  intro x
  have hs : (Fintype.card Ω : ℝ) * μ.mass x = 1 := by
    have h := μ.total
    simp_rw [hc _ x] at h
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  change μ.mass x = 1 / Fintype.card Ω
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (eq_div_iff hn).2
  simpa only [mul_comm] using hs

theorem finiteLaw_uniform_map_equal_fibres
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]
    (f : Ω → Γ) (c : ℕ) (hc : ∀ γ, Fintype.card {ω // f ω = γ} = c) :
    (FiniteLaw.uniform Ω).map f = FiniteLaw.uniform Γ := by
  apply finiteLaw_eq_uniform_of_mass_constant
  intro x y
  have hm (γ : Γ) : ((FiniteLaw.uniform Ω).map f).mass γ =
      (Fintype.card {ω // f ω = γ} : ℝ) * (1 / Fintype.card Ω) := by
    simp [FiniteLaw.map, FiniteLaw.uniform, Fintype.card_subtype, ← Finset.sum_filter]
  rw [hm x, hm y, hc x, hc y]

end Oberwolfach
