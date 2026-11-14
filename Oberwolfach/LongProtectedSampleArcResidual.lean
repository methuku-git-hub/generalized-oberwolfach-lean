module

public import Oberwolfach.LongSelectedTypedPhysicalEdges
public import Oberwolfach.LongSelectedTypedRawDirection
public import Oberwolfach.LongSampledStateOrientationPreserved
public import Oberwolfach.LongEligibleMarkedIncomingChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance protectedSampleArcDecEq : DecidableEq V := Classical.decEq V

theorem long_inner_selected_typed_arcs_survive_residual
    (G Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (I:Finset V)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hDel:∀x∈I,∀y∈I,¬Del.Adj x y)
    (hSmall:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d ω).Adj x y→¬Small.Adj x y):
    ∀x∈I,∀y∈I,
      (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x y=1→
        longEligibleResidualArc M Small ⊥ (x,y)) ∧
      (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1→
        longEligibleResidualArc M Small ⊥ (x,y)):=by
  intro x hx y hy
  constructor
  · intro h
    have hraw:=long_selected_ordinary_raw_direction G π d (fun e=>ω (Sum.inl e)) x y h
    have hM:=long_sampled_state_direction_preserved G Del ω M 0 (by decide) hcorrect x y hraw.1 (hDel x hx y hy)
    have hSel:=long_selected_ordinary_arc_is_physical_edge G π d ω x y h
    exact ⟨hM,hSmall x hx y hy hSel,by simp⟩
  · intro h
    have hraw:=long_selected_marked_raw_direction G π d (fun e=>ω (Sum.inl e)) x y h
    have hM:=long_sampled_state_direction_preserved G Del ω M 1 (by decide) hcorrect x y hraw.1 (hDel x hx y hy)
    have hSel:=long_selected_marked_arc_is_physical_edge G π d ω x y h
    exact ⟨hM,hSmall x hx y hy hSel,by simp⟩
end Oberwolfach
