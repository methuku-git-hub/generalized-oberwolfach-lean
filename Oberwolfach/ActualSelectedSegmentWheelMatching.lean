module

public import Oberwolfach.ActualSelectedSegmentLabels
public import Oberwolfach.MarkedPackingWheelSelection

@[expose] public section
/-! Select distinct original packed wheels for all actual selected segments,
using the common interval-label geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_segments_choose_packed_wheels
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U)
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hex:∀z:actualSelectedSegmentIndex data,∃W∈M,W.2.val=hub ∧ W.1.val 0=(π^z.2.val.val) (root z.1.1.val)):
    ∃W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      (∀z,W z∈M ∧ (W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val)) ∧
      (∀z z',z≠z'→Disjoint (markedWheelPhysicalResources (W z)) (markedWheelPhysicalResources (W z'))):=by
  exact marked_packing_select_distinct_root_wheels tail head ktail khead m b π H₀ Hₖ M hub hpack
    (fun z:actualSelectedSegmentIndex data=>(π^z.2.val.val) (root z.1.1.val))
    (actual_selected_segment_labels_injective data π root hinj hdis) hex
end Oberwolfach
