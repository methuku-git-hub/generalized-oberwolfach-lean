module

public import Oberwolfach.OrientationDisagreementGraph

@[expose] public section
/-! All directed-host hypotheses for the late matching completion follow
from a balanced orientation and its physical correction graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem balanced_host_matching_conditions
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (P Kbad Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (hP:Kbad≤P)
    (hphysical:∀x y,M x y+M y x=if P.Adj x y then 1 else 0)
    (hcorrection:orientationDisagreementGraph P (fun e=>(ω (Sum.inl e)).2) M≤Del):
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
    (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
    (∀x y,M x y=1→P.Adj x y) ∧
    (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→
      ¬Del.Adj x y→M x y=1):=by
  refine ⟨?_,?_,balanced_direction_is_host_edge P M hphysical,?_⟩
  · exact selected_relation_in_balanced_host_after_deletion P π d (fun e=>ω (Sum.inl e)) M Del hcorrection
  · intro x y h
    exact physical_edge_has_balanced_direction P M hphysical x y (hP h)
  · exact approximate_arc_in_balanced_host_after_correction P π d ω M Del hcorrection
end Oberwolfach
