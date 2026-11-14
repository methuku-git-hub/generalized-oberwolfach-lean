module

public import Oberwolfach.MarkedWheelRestriction

@[expose] public section
/-! A marked wheel's physical edge set depends only on its tuple, hub,
and permutation, not on the particular arc witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V} {ktail' khead':K'→V}
  {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ H₀' Hₖ':V→U→Prop}

theorem marked_wheel_same_tuple_same_physical_resources
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (W':MarkedWheel tail' head' ktail' khead' m π b H₀' Hₖ')
    (htuple:W'.1.val=W.1.val) (hhub:W'.2.val=W.2.val):
    markedWheelPhysicalResources W'=markedWheelPhysicalResources W:=by
  unfold markedWheelPhysicalResources
  congr 1
  · unfold markedCyclePhysicalEdges
    congr 1
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply,markedCyclePhysicalEdge_at,htuple]
  · simp only [htuple,hhub]
end Oberwolfach
