module

public import Oberwolfach.SuccessorPreweightExistence
public import Oberwolfach.SeparatedPairWeights

@[expose] public section

/-! The separation step for successor weights, with the distance bound
entering only the final graph-order threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure SuccessorSeparatedWeightConditions {V : Type*} [Fintype V] {k : ℕ}
    (G : SimpleGraph V) (σ : Fin (k+2) → Equiv.Perm V) (π : Equiv.Perm V) (b : ℕ)
    (D τ A B : ℝ) (w : (Fin (k+2) → V × V) → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ w t
  support : ∀ t, 0 < w t → TwistedCyclicTupleValid G σ t ∧ PermutationSeparated π b (pairTupleLabels t)
  upper : ∀ t, w t ≤ B / (Fintype.card V : ℝ) ^ (2*k+2)
  lower : ∀ t, TwistedCyclicTupleValid G σ t → PermutationSeparated π b (pairTupleLabels t) →
    A / (Fintype.card V : ℝ) ^ (2*k+2) ≤ w t
  left : ∀ i x y, ¬ PermutationClose π b x y → G.Adj x y →
    1-τ ≤ (∑ t, if t i = (x,y) then w t else 0) ∧ (∑ t, if t i = (x,y) then w t else 0) ≤ 1
  right : ∀ i x y, ¬ PermutationClose π b x y → G.Adj x (σ i y) →
    1-τ ≤ (∑ t, if ((t i).2,(t (finRotate (k+2) i)).1) = (x,y) then w t else 0) ∧
      (∑ t, if ((t i).2,(t (finRotate (k+2) i)).1) = (x,y) then w t else 0) ≤ 1
  positions : ∀ i v,
    ((1-τ)*D ≤ (∑ t, if (t i).1 = v then w t else 0) ∧
      (∑ t, if (t i).1 = v then w t else 0) ≤ D) ∧
    ((1-τ)*D ≤ (∑ t, if (t i).2 = v then w t else 0) ∧
      (∑ t, if (t i).2 = v then w t else 0) ≤ D)

theorem successor_separation_step {V : Type*} [Fintype V] [Nonempty V] {k : ℕ}
    (G : SimpleGraph V) (σ : Fin (k+2) → Equiv.Perm V) (π : Equiv.Perm V) (b : ℕ)
    (D τ A B : ℝ) (hB : 0 ≤ B) (w : (Fin (k+2) → V × V) → ℝ)
    (hw : SuccessorPreweightConditions G σ D (τ/2) (τ/2) A B w)
    (hvertex : (2*(k+2 : ℝ))^2*(2*b+1)*B ≤ τ*D/2)
    (hedge : (2*(k+2 : ℝ))^2*(2*b+1)*B / Fintype.card V ≤ τ/2) :
    SuccessorSeparatedWeightConditions G σ π b D τ A B (separatedPairWeight π b w) := by
  have hcard : Fintype.card (Fin (k+2) ⊕ Fin (k+2)) = 2*(k+2) := by simp; omega
  have hcardR : (Fintype.card (Fin (k+2) ⊕ Fin (k+2)) : ℝ) = 2*(k+2 : ℝ) := by exact_mod_cast hcard
  have he : Fintype.card (Fin (k+2) ⊕ Fin (k+2))-2 = 2*k+2 := by omega
  have hupper : ∀ t, w t ≤ B / (Fintype.card V : ℝ) ^
      (Fintype.card (Fin (k+2) ⊕ Fin (k+2))-2) := by simpa only [he] using hw.upper
  have hpoint (t : Fin (k+2) → V × V) :
      0 ≤ separatedPairWeight π b w t ∧ separatedPairWeight π b w t ≤ w t := by
    unfold separatedPairWeight
    split_ifs
    · exact ⟨hw.nonneg t,le_rfl⟩
    · exact ⟨le_rfl,hw.nonneg t⟩
  refine ⟨fun t => (hpoint t).1,?_,fun t => (hpoint t).2.trans (hw.upper t),?_,?_,?_,?_⟩
  · intro t ht
    have hs : PermutationSeparated π b (pairTupleLabels t) := by
      by_contra hn
      simp only [separatedPairWeight,hn,ite_false] at ht
      exact (lt_irrefl 0 ht)
    refine ⟨?_,hs⟩
    by_contra hv
    have hz := hw.invalid_zero t hv
    linarith [(hpoint t).2]
  · intro t ht hs
    simp only [separatedPairWeight,hs,ite_true]
    exact hw.lower t ht (permutationSeparated_injective π b _ hs)
  · intro i x y hxy hG
    have h := separatedPairWeight_two_positions π b (by omega : 3 ≤ Fintype.card (Fin (k+2) ⊕ Fin (k+2)))
      (Sum.inl i) (Sum.inr i) (by intro h; cases h) x y hxy w hw.nonneg B hB hupper
    have heq (t : Fin (k+2) → V × V) : t i = (x,y) ↔ (t i).1=x ∧ (t i).2=y := Prod.ext_iff
    simp only [pairTupleLabels,← heq,hcardR] at h
    obtain ⟨hl,hu⟩ := hw.left i x y (fun he => hxy (Or.inl he)) hG
    exact ⟨by linarith [h.1],h.2.trans hu⟩
  · intro i x y hxy hG
    have h := separatedPairWeight_two_positions π b (by omega : 3 ≤ Fintype.card (Fin (k+2) ⊕ Fin (k+2)))
      (Sum.inr i) (Sum.inl (finRotate (k+2) i)) (by intro h; cases h) x y hxy w hw.nonneg B hB hupper
    have heq (t : Fin (k+2) → V × V) : ((t i).2,(t (finRotate (k+2) i)).1) = (x,y) ↔
        (t i).2=x ∧ (t (finRotate (k+2) i)).1=y := by simp only [Prod.mk.injEq]
    simp only [pairTupleLabels,← heq,hcardR] at h
    obtain ⟨hl,hu⟩ := hw.right i x y (fun he => hxy (Or.inl he)) hG
    exact ⟨by linarith [h.1],h.2.trans hu⟩
  · intro i v
    have h₁ := separatedPairWeight_one_position π b (by omega : 2 ≤ Fintype.card (Fin (k+2) ⊕ Fin (k+2)))
      (Sum.inl i) v w hw.nonneg B hB hupper
    have h₂ := separatedPairWeight_one_position π b (by omega : 2 ≤ Fintype.card (Fin (k+2) ⊕ Fin (k+2)))
      (Sum.inr i) v w hw.nonneg B hB hupper
    simp only [pairTupleLabels,hcardR] at h₁ h₂
    obtain ⟨⟨hl₁,hu₁⟩,⟨hl₂,hu₂⟩⟩ := hw.positions i v
    exact ⟨⟨by nlinarith [h₁.1],h₁.2.trans hu₁⟩,⟨by nlinarith [h₂.1],h₂.2.trans hu₂⟩⟩

theorem successor_separated_weight_existence (k : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∀ τ : ℝ, 0 < τ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ b : ℕ, ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [Nonempty V], N ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (π : Equiv.Perm V) (mark : Fin (k+2) → Bool) (D : ℝ),
      (Fintype.card V : ℝ)/2 ≤ D → D ≤ 2*Fintype.card V →
      (∀ v, |(G.degree v : ℝ)-D| ≤ ε₀*Fintype.card V) →
      (∀ v, (successorCycleRatio k + β)*Fintype.card V ≤ (G.degree v : ℝ)) →
      ∃ w, SuccessorSeparatedWeightConditions G (fun i => choosePermutation π (mark i)) π b D τ
        (successorWeightLower k β) (successorWeightUpper k β) w := by
  intro τ hτ
  obtain ⟨ε₀,hε₀,N₀,hN₀⟩ := successor_preweight_existence k β hβ τ hτ
  refine ⟨ε₀,hε₀,?_⟩
  intro b
  let B := successorWeightUpper k β
  have hB : 0 < B := (successorWeightConstants_pos k β hβ).2
  let M := (2*(k+2 : ℝ))^2*(2*b+1)*B
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N₁,hN₁⟩ := eventually_reciprocal_small (τ/(4*M)) (by positivity)
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ hn G π mark D hD hDup hnear hmin
  obtain ⟨w,hw⟩ := hN₀ V ((le_max_left _ _).trans hn) G π mark D hD hDup hnear hmin
  have hrec := (hN₁ (Fintype.card V) ((le_max_right _ _).trans hn)).2
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hMsmall : M / Fintype.card V ≤ τ/4 := by
    have hh := mul_le_mul_of_nonneg_left hrec hM.le
    have he : M * (τ/(4*M)) = τ/4 := by field_simp
    rw [he] at hh
    simpa only [mul_one_div] using hh
  have hMvertex : M ≤ τ*D/2 := by
    have hh := (div_le_iff₀ hnR).mp hMsmall
    have hd := mul_le_mul_of_nonneg_left hD hτ.le
    nlinarith
  exact ⟨separatedPairWeight π b w,successor_separation_step G _ π b D τ _ B hB.le w hw
    hMvertex (by dsimp [M] at hMsmall; linarith)⟩

end Oberwolfach
