module

public import Oberwolfach.OrdinaryInnerParentTriangleWeights
public import Oberwolfach.OrdinaryInducedParentThreshold

@[expose] public section
/-! The deterministic parent inner-neighborhood density suffices to select
bounded fractional inner triangle weights before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_triangle_weights_from_parent_density
    (α : ℝ) (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (A : Finset V), N ≤ A.card →
      ∀ (P : SimpleGraph V) (density : ℝ), cycleThreshold 3 + α ≤ density →
        (∀ v, density*A.card ≤ ((A ∩ P.neighborFinset v).card : ℝ)) →
      ∃ weight : OrdinaryCycle (P.induce (A : Set V)) 3 → ℝ,
        (∀ C₀, c / A.card ≤ weight C₀ ∧ weight C₀ ≤ C / A.card) ∧
        (∀ x y, (∑ C₀, if C₀.val.val.Adj x y then weight C₀ else 0) =
          if (P.induce (A : Set V)).Adj x y then 1 else 0) := by
  obtain ⟨c,C,hc,hC,N,hN,hweights⟩ := ordinary_inner_parent_triangle_weights_from_threshold α hα
  refine ⟨c,C,hc,hC,N,hN,?_⟩
  intro V _ _ A hn P density hthreshold hmin
  apply hweights V A hn P
  exact ordinary_induced_parent_threshold_from_density P A density α hthreshold hmin
end Oberwolfach
