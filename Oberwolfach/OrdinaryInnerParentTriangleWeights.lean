module

public import Oberwolfach.AlmostSpanningCyclePacking

@[expose] public section
/-! Choose positive fractional triangle weights on the fixed inner graph
before sampling, using its actual induced minimum-degree hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_parent_triangle_weights_from_threshold
    (α : ℝ) (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (A : Finset V), N ≤ A.card →
      ∀ P : SimpleGraph V,
        (∀ v : {x : V // x ∈ (A : Set V)},
          (cycleThreshold 3 + α) * A.card ≤ ((P.induce (A : Set V)).degree v : ℝ)) →
      ∃ weight : OrdinaryCycle (P.induce (A : Set V)) 3 → ℝ,
        (∀ C₀, c / A.card ≤ weight C₀ ∧ weight C₀ ≤ C / A.card) ∧
        (∀ x y, (∑ C₀, if C₀.val.val.Adj x y then weight C₀ else 0) =
          if (P.induce (A : Set V)).Adj x y then 1 else 0) := by
  obtain ⟨c,C,hc,hC,N,hN,hweights⟩ := positive_ordinary_fractional_cycle_weights 3 (by omega) α hα
  refine ⟨c,C,hc,hC,N,hN,?_⟩
  intro V _ _ A hn P hdeg
  have hcard : Fintype.card {x : V // x ∈ (A : Set V)} = A.card := by simp
  obtain ⟨weight,hw,he⟩ := hweights {x : V // x ∈ (A : Set V)} (by simpa only [hcard] using hn)
    (P.induce (A : Set V)) (by
      intro v
      convert hdeg v using 1 <;> simp only [hcard])
  refine ⟨weight,?_,?_⟩
  · intro C₀
    simpa only [show 3-2=1 by omega, pow_one, hcard] using hw C₀
  · exact ordinary_cycle_incidence_load_adjacency _ 3 weight he
end Oberwolfach
