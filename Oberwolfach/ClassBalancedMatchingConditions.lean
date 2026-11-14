module

public import Oberwolfach.ExpandedClassCorrectionArcs

@[expose] public section
/-! The actual class orientation supplies the directed matching hypotheses,
while its correction is charged only to sampled class edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_balanced_matching_conditions
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S Kbad Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (M:V→V→ℕ)
    (hSP:S≤P) (hKbad:Kbad≤S)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph P σ {0,1,2,3,4})
      (fun e=>(σ (Sum.inl e)).2) M≤Del):
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
    (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
    (∀x y,M x y=1→P.Adj x y) ∧
    (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) x y→
      ¬Del.Adj x y→M x y=1):=by
  refine ⟨?_,?_,?_,?_⟩
  · intro x y h hDel
    have hh:=selected_arc_sampled_class P π d σ x y h
    exact sampled_class_arc_follows_corrected_orientation _ Del _ M hcorrect x y hh.1 hh.2 hDel
  · intro x y h
    exact physical_edge_has_balanced_direction S M hphysical x y (hKbad h)
  · intro x y h
    exact hSP (balanced_direction_is_host_edge S M hphysical x y h)
  · intro x y h hDel
    have hh:=approximate_arc_sampled_class P π d σ x y h
    exact sampled_class_arc_follows_corrected_orientation _ Del _ M hcorrect x y hh.1 hh.2 hDel
end Oberwolfach
