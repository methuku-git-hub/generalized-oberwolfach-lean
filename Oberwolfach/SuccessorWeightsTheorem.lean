module

public import Oberwolfach.SuccessorSequenceWeights

@[expose] public section

/-! The manuscript successor-weight theorem for every even cycle length.
Weights are extended by zero outside the valid separated tuples; this is
equivalent to weighting only the family appearing in the manuscript. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem successorCycleRatio_standard (k : ℕ) :
    successorCycleRatio k = (((k+2)*2 : ℕ) : ℝ) / (2*(((k+2)*2 : ℕ) : ℝ)-2) := by
  have hd : (2*(k+2 : ℝ)-1) ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hd' : (2*(((k+2)*2 : ℕ) : ℝ)-2) ≠ 0 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  unfold successorCycleRatio
  push_cast
  field_simp

theorem successor_weights_theorem (c : ℕ) (hc : 4 ≤ c) (heven : Even c)
    (β : ℝ) (hβ : 0 < β) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ τ : ℝ, 0 < τ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ b : ℕ, 2 ≤ b → ∃ N : ℕ,
      ∀ (V : Type) [Fintype V], N ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (π : Equiv.Perm V) (D : ℝ),
      (Fintype.card V : ℝ)/2 ≤ D → D ≤ 2*Fintype.card V →
      (∀ v, |(G.degree v : ℝ)-D| ≤ ε₀*Fintype.card V) →
      (∀ v, ((c : ℝ)/(2*c-2)+β)*Fintype.card V ≤ (G.degree v : ℝ)) →
      ∃ w : (Fin c → V) → ℝ, SuccessorSequenceWeightConditions G π b D τ A B w := by
  obtain ⟨k,hk⟩ : ∃ k : ℕ, c=(k+2)*2 := by
    obtain ⟨r,hr⟩ := heven
    refine ⟨r-2,?_⟩
    omega
  subst c
  obtain ⟨hA,hB⟩ := successorWeightConstants_pos k β hβ
  refine ⟨successorWeightLower k β,successorWeightUpper k β,hA,hB,?_⟩
  intro τ hτ
  obtain ⟨ε₀,hε₀,hall⟩ := successor_sequence_weight_existence k β hβ τ hτ
  refine ⟨ε₀,hε₀,?_⟩
  intro b _
  obtain ⟨N,hN⟩ := hall b
  refine ⟨max N 1,?_⟩
  intro V _ hn G π D hD hDup hnear hmin
  have hv : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hv
  exact hN V ((le_max_left _ _).trans hn) G π D hD hDup hnear
    (by simpa only [successorCycleRatio_standard] using hmin)

end Oberwolfach
