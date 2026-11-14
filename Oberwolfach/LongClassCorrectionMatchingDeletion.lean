module

public import Oberwolfach.ClassCorrectionMatchingDeletion
public import Oberwolfach.ExpandedClassCorrectionArcs

@[expose] public section
/-! The actual long-class sample supplies the class-membership premise for
every approximate physical arc, so the same deletion budget aligns them all. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_class_correction_matching_deletion
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P S D₀:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (ξ δ η:ℝ):
    let S₀:=longPhysicalStateGraph P ω {0,1,2,3,4};
    (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*Fintype.card V)→
    (∀v,((orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*Fintype.card V)→
    (∀v,(D₀.degree v:ℝ)≤η*Fintype.card V)→
    ∃Del:SimpleGraph V,D₀≤Del ∧
      (∀v,(Del.degree v:ℝ)≤(η+ξ+δ)*Fintype.card V) ∧
      (∀x y,S₀.Adj x y→¬Del.Adj x y→S.Adj x y) ∧
      (∀x y,rawMixedPhysicalArc P π d
        (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1):=by
  intro S₀ hedit hcorrect hD₀
  have hP:S₀≤P:=by intro x y h;exact h.1
  obtain ⟨Del,hD,hdeg,hinside,halign⟩:=class_correction_matching_deletion P S₀ S D₀ π d ω M ξ δ η hP hedit hcorrect hD₀
  refine ⟨Del,hD,hdeg,hinside,?_⟩
  intro x y harc hnot
  have hh:=approximate_arc_sampled_class P π d ω x y harc
  exact halign x y hh.1 harc hnot
end Oberwolfach
