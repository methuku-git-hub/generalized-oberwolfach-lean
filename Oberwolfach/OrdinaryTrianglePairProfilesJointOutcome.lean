module

public import Oberwolfach.OrdinaryTrianglePairProfilesJointEvent
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_pair_profiles_joint_outcome_from_inputs
    (β a b η L pmin smin:ℝ) (hβ:0<β) (hL:0≤L):
    let cmin:=pmin^3*(smin*smin)^2;
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color),
    (∀ v,(F.degree v:ℝ)≤L) → ∀ μ:FiniteLaw (RawWheelOutcome V U Γ Color),
    ∀ (E:RawWheelOutcome V U Γ Color→Prop) (δ:ℝ),
    1-δ ≤ μ.probability (ordinarySampledTriangleProfileProperty P F π d · pmin smin j β η a b) →
    δ < μ.probability E → ∃ σ, E σ ∧ (fun σ=>Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
      (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4) a (4*b/cmin) η)) σ := by
  intro cmin
  obtain ⟨N,hN⟩:=ordinary_triangle_pair_profiles_joint_event_from_inputs β a b η L pmin smin hβ hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P F π d j hF μ E δ hgood hlarge
  have hjoint:=hN V U Γ Color hn P F π d j hF μ E δ hgood
  have hpos:0<μ.probability (fun σ=>E σ ∧ (fun σ=>Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
      (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4) a (4*b/cmin) η)) σ):=by linarith
  obtain ⟨σ,_,hσ⟩:=finiteLaw_positive_event_exists μ _ hpos
  exact ⟨σ,hσ⟩
end Oberwolfach
