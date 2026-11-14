module

public import Oberwolfach.OrdinaryTrianglePropertyToProfiles
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! The triangular profile construction preserves the same sample-level event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_pair_profiles_probability_from_inputs
    (β a b η L pmin smin:ℝ) (hβ:0<β) (hL:0≤L):
    let cmin:=pmin^3*(smin*smin)^2;
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color),
    (∀ v,(F.degree v:ℝ)≤L) → ∀ μ:FiniteLaw (RawWheelOutcome V U Γ Color),
    μ.probability (ordinarySampledTriangleProfileProperty P F π d · pmin smin j β η a b) ≤
    μ.probability (fun σ=>Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
      (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4) a (4*b/cmin) η)) := by
  intro cmin
  obtain ⟨N,hN⟩:=ordinary_triangle_property_to_pair_profiles β a b η L pmin smin hβ hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P F π d j hF μ
  apply finiteLaw_probability_mono
  intro σ hσ
  exact hN V U Γ Color hn P F π d σ j hF hσ
end Oberwolfach
