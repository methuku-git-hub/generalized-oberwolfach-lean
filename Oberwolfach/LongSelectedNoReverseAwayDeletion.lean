module

public import Oberwolfach.LongSelectedTypedDirectionAwayDeletion

@[expose] public section
/-! Outside the orientation-deletion graph, a selected arc cannot point
against the class orientation, in either selected type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_selected_no_reverse_away_deletion
    (G S Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (x y:V) (hM:M x y=1) (hDel:¬Del.Adj x y):
    markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false y x≠1 ∧
    markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true y (π.symm x)≠1:=by
  have hno:M y x≠1:=by
    intro hy
    have hh:=hphysical x y
    split_ifs at hh <;> omega
  have hDel':¬Del.Adj y x:=fun h=>hDel h.symm
  constructor
  · intro h
    have hh:=long_selected_ordinary_raw_direction G π d (fun e=>ω (Sum.inl e)) y x h
    exact hno (long_sampled_state_direction_preserved G Del ω M 0 (by decide) hcorrect y x hh.1 hDel')
  · intro h
    have hh:=long_selected_marked_raw_direction G π d (fun e=>ω (Sum.inl e)) y x h
    exact hno (long_sampled_state_direction_preserved G Del ω M 1 (by decide) hcorrect y x hh.1 hDel')
end Oberwolfach
