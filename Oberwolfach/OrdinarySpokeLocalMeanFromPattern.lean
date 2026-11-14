module

public import Oberwolfach.OrdinarySpokePatternExpectationLocal

@[expose] public section
/-! A fixed wheel spoke mean gives the corresponding local cycle-potential
mean without expanding the finite wheel type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]

theorem ordinary_spoke_local_mean_from_pattern
    (P F : SimpleGraph V) (r : ℕ) (φ : OrdinaryCycle P r → ℝ)
    (μ : FiniteLaw Ω) (Q : Ω → SimpleGraph V) (H : Ω → V → U → Prop) (v : V) (u : U) (k : ℝ)
    (hmean : μ.expectation (fun σ => resourcePatternLoad ordinaryWheelResources
      (ordinaryCycleWheelWeight P F r φ 1) (fun _ _ => true) (Sum.inr (v,u))
      (ordinaryResourceState (Q σ) (H σ))) =
      k * ordinarySpokeLoad (ordinaryCycleWheelWeight P F r φ 1) v u) :
    μ.expectation (fun σ => ordinaryLocalPotential P (Q σ) F
      (Finset.univ.filter (fun z => H σ z u)) φ v) =
      k * ∑ C, if v ∈ C.val.val.support ∧
        (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then φ C else 0 := by
  have hbridge := ordinary_spoke_pattern_expectation_local P F r φ 1 μ Q H v u
  simp only [div_one] at hbridge
  rw [←hbridge, hmean, ordinaryCycleWheelWeight_spoke_load]
  simp only [one_div, inv_one, one_mul]
end Oberwolfach
