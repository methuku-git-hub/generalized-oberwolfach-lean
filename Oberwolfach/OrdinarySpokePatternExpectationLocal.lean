module

public import Oberwolfach.OrdinaryPatternSpokeLocalBridge
public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Taking expectations preserves the exact spoke-pattern/local-potential
identity, for any finite sample law and arbitrary random graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]

theorem ordinary_spoke_pattern_expectation_local
    (P F : SimpleGraph V) (r : ℕ) (weight : OrdinaryCycle P r → ℝ) (D : ℝ)
    (μ : FiniteLaw Ω) (Q : Ω → SimpleGraph V) (H : Ω → V → U → Prop) (v : V) (u : U) :
    μ.expectation (fun σ => resourcePatternLoad ordinaryWheelResources
      (ordinaryCycleWheelWeight P F r weight D) (fun _ _ => true) (Sum.inr (v,u))
      (ordinaryResourceState (Q σ) (H σ))) =
    μ.expectation (fun σ => ordinaryLocalPotential P (Q σ) F
      (Finset.univ.filter (fun z => H σ z u)) (fun C => weight C / D) v) := by
  congr 1
  funext σ
  exact ordinary_pattern_spoke_eq_local_bridge P (Q σ) F (H σ) weight D v u
end Oberwolfach
