module

public import Oberwolfach.LongNamedReservedCorrectionUniformLists

@[expose] public section
/-! Apply the matching and reserved-list continuations to the same deletion
without changing the selected positive-mass outcome or its other properties. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_same_sample_matching_and_lists_after_deletion
    (n:ℕ) (Ω:Type) (mass:Ω→ℝ) (Good:Ω→Prop)
    (Match:Ω→SimpleGraph (Fin n)→ℝ→Prop)
    (Lists:Ω→SimpleGraph (Fin n)→Finset (Fin n)→Prop)
    (Δ ζ ε:ℝ) (hζΔ:ζ≤Δ)
    (hSample:∃z,0<mass z ∧ Good z ∧
      (∀(Del:SimpleGraph (Fin n)) (δ:ℝ),(∀x,(Del.degree x:ℝ)≤δ)→δ≤Δ*n→Match z Del δ) ∧
      (∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
        ∀Inner:Finset (Fin n),(Inner.card:ℝ)≤ε*n→Lists z Del Inner)):
    ∃z,0<mass z ∧ Good z ∧
      ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
        Match z Del (ζ*n) ∧ ∀Inner:Finset (Fin n),(Inner.card:ℝ)≤ε*n→Lists z Del Inner := by
  obtain ⟨z,hm,hgood,hmatch,hlists⟩:=hSample
  refine ⟨z,hm,hgood,?_⟩
  intro Del hDel
  refine ⟨hmatch Del (ζ*n) hDel ?_,hlists Del hDel⟩
  exact mul_le_mul_of_nonneg_right hζΔ (Nat.cast_nonneg n)
end Oberwolfach
