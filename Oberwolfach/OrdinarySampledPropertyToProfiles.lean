module

public import Oberwolfach.OrdinarySampledProfileProperty
public import Oberwolfach.OrdinaryPairProfilesHighDomainExplicit

@[expose] public section
/-! The checked sample-level inputs supply the longer-cycle pair profiles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_sampled_property_to_pair_profiles (m:ℕ) (hm:3≤m)
    (β a b η L pmin smin:ℝ) (hβ:0<β) (hL:0≤L):
    let cmin:=pmin^(m+1)*(smin*smin)^m;
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color) (j:Color),
    (∀ v,(F.degree v:ℝ)≤L) →
    ordinarySampledProfileProperty (r:=m+1) P F π d σ pmin smin j β η a b →
    Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) (m+1)
      (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β ((ordinaryLocalCountCoeff m β/2)^(m+2)) a (4*b/cmin) η) := by
  intro cmin
  obtain ⟨N,hN⟩:=ordinary_pair_profiles_from_high_domain_explicit m hm β a (4*b/cmin) η L hβ hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P F π d σ j hF hProp
  dsimp [ordinarySampledProfileProperty] at hProp
  obtain ⟨hpair,w,hw,hdeg⟩:=hProp
  refine hN V U hn (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) hF ?_ w ?_ ?_
  · exact hpair
  · intro u u' hne C
    have hh:=hw u u' hne C
    simpa only [Nat.add_sub_cancel] using hh
  · exact hdeg
end Oberwolfach
