module

public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section
/-! The selected rim projection leaves every interval coordinate unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_reference_spoke_projection
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (j:Color) (v:V) (u:U):
    rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) j v u ↔
      rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (v,u)=some (Sum.inr j):=by
  rfl
end Oberwolfach
