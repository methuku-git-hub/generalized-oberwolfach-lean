module

public import Oberwolfach.ColourRetentionCoins
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Expanding joint clique-retention events into choices of the unique
retained vertex in each clique. Overlapping cliques are allowed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem clique_retained_indicator_sum {V C : Type*}
    (G : SimpleGraph V) (T : Finset V)
    (hT : ∀ u∈T,∀ v∈T,u≠v → G.Adj u v) (σ : V → C×Bool) (c : C) :
    (∑ v : {v // v∈T},if coinRetainedColour G σ v.val=some c then (1 : ℝ) else 0)=
      if ∃ v∈T,coinRetainedColour G σ v=some c then 1 else 0 := by
  classical
  by_cases h : ∃ v∈T,coinRetainedColour G σ v=some c
  · obtain ⟨v,hv,hkeep⟩ := h
    rw [if_pos ⟨v,hv,hkeep⟩]
    have hother (u : {v // v∈T}) (hne : u≠⟨v,hv⟩) :
        coinRetainedColour G σ u.val≠some c := by
      have huv : u.val≠v := fun he=>hne (Subtype.ext he)
      exact coinRetainedColour_proper G σ (hT v hv u.val u.property (Ne.symm huv)) c hkeep
    rw [Finset.sum_eq_single ⟨v,hv⟩]
    · simp [hkeep]
    · intro u _ hu
      simp [hother u hu]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (fun hc=>h ⟨v.val,v.property,hc⟩)

theorem clique_joint_retention_expansion
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (T : J → Finset V)
    (hT : ∀ j,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (μ : FiniteLaw (V → C×Bool)) (c : C) :
    μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)=
      ∑ f : (j : J) → {v // v∈T j},
        μ.probability (fun σ=>∀ j,coinRetainedColour G σ (f j).val=some c) := by
  classical
  have he (σ : V → C×Bool) :
      (if ∀ j,∃ v∈T j,coinRetainedColour G σ v=some c then (1 : ℝ) else 0)=
        ∑ f : (j : J) → {v // v∈T j},
          (if ∀ j,coinRetainedColour G σ (f j).val=some c then 1 else 0) := by
    rw [← Fintype.prod_boole]
    have hc (j : J) := (clique_retained_indicator_sum G (T j) (hT j) σ c).symm
    simp_rw [hc]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f _
    exact Fintype.prod_boole
  rw [finiteLaw_probability_eq_expectation]
  simp_rw [he]
  unfold FiniteLaw.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  unfold FiniteLaw.probability
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : ∀ j,coinRetainedColour G σ (f j).val=some c <;> simp [h]

end Oberwolfach
