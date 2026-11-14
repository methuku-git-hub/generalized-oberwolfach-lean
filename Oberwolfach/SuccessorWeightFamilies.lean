module

public import Oberwolfach.SuccessorSequenceWeights

@[expose] public section

/-! Domain-specific successor weights chosen simultaneously before any
sampling. The near-regularity tolerance precedes the separation parameter;
the positive coefficient constants do not depend on the positional error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem successor_sequence_weight_families (k m : ℕ) (hlen : m+1=(k+2)*2)
    (β τ : ℝ) (hβ : 0<β) (hτ : 0<τ) :
    ∃ δ : ℝ,0<δ ∧ ∀ b : ℕ,∃ N : ℕ,1≤N ∧
    ∀ (W : ℕ→Type) [∀ i,Fintype (W i)]
      (G : ∀ i,SimpleGraph (W i)) (π : ∀ i,Equiv.Perm (W i)) (D : ℕ→ℝ) (L : ℕ),
      (∀ i≤L,N≤Fintype.card (W i)) →
      (∀ i≤L,(Fintype.card (W i):ℝ)/2≤D i) →
      (∀ i≤L,D i≤2*Fintype.card (W i)) →
      (∀ i≤L,∀ v,|((G i).degree v:ℝ)-D i|≤δ*Fintype.card (W i)) →
      (∀ i≤L,∀ v,(successorCycleRatio k+β)*Fintype.card (W i)≤((G i).degree v:ℝ)) →
      ∃ weight : ∀ i,(Fin (m+1)→W i)→ℝ,
        ∀ i≤L,SuccessorSequenceWeightConditions (G i) (π i) b (D i) τ
          (successorWeightLower k β) (successorWeightUpper k β) (weight i) := by
  obtain ⟨δ,hδ,hall⟩ := successor_sequence_weight_existence k β hβ τ hτ
  refine ⟨δ,hδ,?_⟩
  intro b
  obtain ⟨N,hN⟩ := hall b
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro W _ G π D L hn hDlo hDhi hnear hmin
  have hex (i : ℕ) : ∃ w : (Fin (m+1)→W i)→ℝ,i≤L →
      SuccessorSequenceWeightConditions (G i) (π i) b (D i) τ
        (successorWeightLower k β) (successorWeightUpper k β) w := by
    by_cases hi : i≤L
    · have hnpos : 0<Fintype.card (W i) := by have hh:=hn i hi;omega
      letI : Nonempty (W i) := Fintype.card_pos_iff.mp hnpos
      have hh := hN (W i) ((le_max_right 1 N).trans (hn i hi)) (G i) (π i) (D i)
        (hDlo i hi) (hDhi i hi) (hnear i hi) (hmin i hi)
      rw [← hlen] at hh
      obtain ⟨w,hw⟩ := hh
      exact ⟨w,fun _=>hw⟩
    · exact ⟨fun _=>0,fun hi'=>False.elim (hi hi')⟩
  choose weight hw using hex
  exact ⟨weight,hw⟩

end Oberwolfach
