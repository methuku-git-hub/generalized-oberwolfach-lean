module

public import Oberwolfach.OrdinarySampledTriangleProfileProperty
public import Oberwolfach.OrdinaryTriangleProfilesHighDomainExplicit

@[expose] public section
/-! The checked sampled triangle inputs supply the triangular pair profiles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_triangle_property_to_pair_profiles
    (β a b η L pmin smin:ℝ) (hβ:0<β) (hL:0≤L):
    let cmin:=pmin^3*(smin*smin)^2;
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color) (j:Color),
    (∀ v,(F.degree v:ℝ)≤L) →
    ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b →
    Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
      (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4) a (4*b/cmin) η) := by
  intro cmin
  obtain ⟨N,hN⟩:=ordinary_triangle_profiles_from_high_domain_explicit β a (4*b/cmin) η L hβ hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P F π d σ j hF hProp
  dsimp [ordinarySampledTriangleProfileProperty] at hProp
  obtain ⟨hfour,w,hw,hdeg⟩:=hProp
  refine hN V U hn (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) hF ?_ w ?_ ?_
  · exact hfour
  · intro u u' hne C
    exact hw u u' hne C
  · exact hdeg
end Oberwolfach
