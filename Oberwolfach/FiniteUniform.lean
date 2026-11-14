module

public import Oberwolfach.SamplingRestriction
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

/-! Uniform finite laws and exposure by a first choice followed by a
conditional finite law. The second law may depend on the first choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

instance finiteSigmaNonempty {Ω : Type*} [Nonempty Ω] {Γ : Ω → Type*}
    [∀ ω, Nonempty (Γ ω)] : Nonempty (Σ ω, Γ ω) :=
  ⟨⟨Classical.choice (inferInstance : Nonempty Ω), Classical.choice inferInstance⟩⟩

namespace FiniteLaw

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := 1 / Fintype.card Ω
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

def sigma {Ω : Type*} [Fintype Ω] {Γ : Ω → Type*} [∀ ω, Fintype (Γ ω)]
    (μ : FiniteLaw Ω) (ν : ∀ ω, FiniteLaw (Γ ω)) : FiniteLaw (Σ ω, Γ ω) where
  mass p := μ.mass p.1 * (ν p.1).mass p.2
  nonneg p := mul_nonneg (μ.nonneg _) ((ν p.1).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, (ν _).total, mul_one]
    exact μ.total

end FiniteLaw

theorem finiteLaw_uniform_expectation {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) :
    (FiniteLaw.uniform Ω).expectation X = (∑ ω, X ω) / Fintype.card Ω := by
  simp only [FiniteLaw.expectation, FiniteLaw.uniform, ← Finset.mul_sum]
  ring

theorem finiteLaw_uniform_map_equiv
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]
    (e : Ω ≃ Γ) : (FiniteLaw.uniform Ω).map e = FiniteLaw.uniform Γ := by
  apply finiteLaw_ext
  intro γ
  dsimp only [FiniteLaw.map, FiniteLaw.uniform]
  rw [← e.symm.sum_comp]
  simp only [e.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Fintype.card_congr e]

theorem finiteLaw_sigma_expectation
    {Ω : Type*} [Fintype Ω] {Γ : Ω → Type*} [∀ ω, Fintype (Γ ω)]
    (μ : FiniteLaw Ω) (ν : ∀ ω, FiniteLaw (Γ ω)) (X : (Σ ω, Γ ω) → ℝ) :
    (μ.sigma ν).expectation X =
      μ.expectation (fun ω => (ν ω).expectation (fun γ => X ⟨ω, γ⟩)) := by
  unfold FiniteLaw.expectation
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  change (μ.mass ω * (ν ω).mass γ) * X ⟨ω, γ⟩ = μ.mass ω * ((ν ω).mass γ * X ⟨ω, γ⟩)
  ring

theorem finiteLaw_uniform_sigma_equal_fibres
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] {Γ : Ω → Type*}
    [∀ ω, Fintype (Γ ω)] [∀ ω, Nonempty (Γ ω)]
    (c : ℕ) (hcard : ∀ ω, Fintype.card (Γ ω) = c) :
    (FiniteLaw.uniform Ω).sigma (fun ω => FiniteLaw.uniform (Γ ω)) =
      FiniteLaw.uniform (Σ ω, Γ ω) := by
  apply finiteLaw_ext
  intro p
  dsimp only [FiniteLaw.sigma, FiniteLaw.uniform]
  rw [hcard, Fintype.card_sigma]
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
  ring

theorem finiteLaw_map_expectation
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (f : Ω → Γ) (X : Γ → ℝ) :
    (μ.map f).expectation X = μ.expectation (fun ω => X (f ω)) := by
  unfold FiniteLaw.expectation
  dsimp only [FiniteLaw.map]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  have hh (γ : Γ) : (if f ω = γ then μ.mass ω else 0) * X γ =
      if f ω = γ then μ.mass ω * X (f ω) else 0 := by
    by_cases h : f ω = γ <;> simp [h]
  simp_rw [hh]
  simp

end Oberwolfach
