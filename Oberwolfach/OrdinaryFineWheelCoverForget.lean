module

public import Oberwolfach.OrdinaryFineWheelCoverResult
public import Oberwolfach.OrdinaryNonrootWheelCoverResult

@[expose] public section
/-! Forgetting the extra crossing bound retains the original cover witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]

theorem ordinary_fine_wheel_cover_forget
    (m K:ℕ) (ξ aLoad:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (I T:Finset V) (B W:Finset U)
    (h:OrdinaryFineWheelCoverResult m K ξ aLoad Q F H I T B W):
    OrdinaryNonrootWheelCoverResult m K ξ aLoad Q F H I T B W:=by
  obtain ⟨D,J,hD,hDt,hJ,hbal,hdiv,hdegree,M,hpair,hinner,hr,hs,hcol,hleft,hright,hcross,havoid⟩:=h
  exact ⟨D,J,hD,hDt,hJ,hbal,hdiv,hdegree,M,hpair,hinner,hr,hs,hcol,hleft,hright,havoid⟩
end Oberwolfach
