module

public import Oberwolfach.ClassCorrectionDeletionContainsEdits
public import Oberwolfach.ClassBalancedMatchingConditions

@[expose] public section
/-! The original sampled matching can be used after regularisation and
orientation correction: the same deletion has the combined degree budget,
and it supplies all four directed matching compatibility conditions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_class_matching_after_correction
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P S Kbad D₀:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (ξ δ η:ℝ):
    let S₀:=longPhysicalStateGraph P ω {0,1,2,3,4};
    S≤P→Kbad≤S→(∀x y,M x y+M y x=if S.Adj x y then 1 else 0)→
    (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*Fintype.card V)→
    (∀v,((orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*Fintype.card V)→
    (∀v,(D₀.degree v:ℝ)≤η*Fintype.card V)→
    ∃Del:SimpleGraph V,D₀≤Del ∧ (S₀\S)≤Del ∧
      orientationDisagreementGraph S₀ (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
      (∀v,(Del.degree v:ℝ)≤(η+ξ+δ)*Fintype.card V) ∧
      (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
      (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
      (∀x y,M x y=1→P.Adj x y) ∧
      (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→
        ¬Del.Adj x y→M x y=1):=by
  intro S₀ hSP hKbad hphysical hedit hcorrect hD₀
  have hP:S₀≤P:=by intro x y h;exact h.1
  obtain ⟨Del,hD,hedits,hinc,hdegree,_,_⟩:=class_correction_matching_deletion_contains_edits
    P S₀ S D₀ π d ω M ξ δ η hP hedit hcorrect hD₀
  have hconditions:=class_balanced_matching_conditions P S Kbad Del π d ω M hSP hKbad hphysical hinc
  exact ⟨Del,hD,hedits,hinc,hdegree,hconditions⟩
end Oberwolfach
