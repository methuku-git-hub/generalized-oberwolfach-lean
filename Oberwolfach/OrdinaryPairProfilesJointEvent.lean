module

public import Oberwolfach.OrdinarySampledPropertyToProfiles
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! The profile construction preserves the probability of the existing
sample-level event; no resampling or independence is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_pair_profiles_joint_event_from_inputs (m:ℕ) (hm:3≤m)
    (β a b η L pmin smin:ℝ) (hβ:0<β) (hL:0≤L):
    let cmin:=pmin^(m+1)*(smin*smin)^m;
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (j:Color),
    (∀ v,(F.degree v:ℝ)≤L) → ∀ μ:FiniteLaw (RawWheelOutcome V U Γ Color),
    ∀ (E:RawWheelOutcome V U Γ Color→Prop) (δ:ℝ),
    1-δ ≤ μ.probability (ordinarySampledProfileProperty (r:=m+1) P F π d · pmin smin j β η a b) →
    μ.probability E-δ ≤ μ.probability (fun σ=>E σ ∧ (fun σ=>Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) (m+1)
      (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β ((ordinaryLocalCountCoeff m β/2)^(m+2)) a (4*b/cmin) η)) σ) := by
  intro cmin
  obtain ⟨N,hN⟩:=ordinary_sampled_property_to_pair_profiles m hm β a b η L pmin smin hβ hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P F π d j hF μ E δ hgood
  apply le_trans (finiteLaw_good_intersection μ E _ δ hgood)
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.1,hN V U Γ Color hn P F π d σ j hF hσ.2⟩
end Oberwolfach
