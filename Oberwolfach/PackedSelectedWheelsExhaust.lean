module

public import Oberwolfach.PackedPhysicalSpokePositions
public import Oberwolfach.ActualSelectedSegmentLabels
public import Oberwolfach.ResidualRunContainingSegment

@[expose] public section
/-! Every packed marked wheel whose marked root lies on an approximate
interval is the wheel chosen for the corresponding selected segment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem packed_marked_wheels_exhaust_selected_segments
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (S:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (w:U) (root:K→V)
    (hHub:∀W∈S,W.2.val=w)
    (hDis:∀W∈S,∀Z∈S,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hT:∀i∈data.s₂,data.T i=packedPhysicalSpokePositions tail head ktail khead m b data.d π H₀ Hₖ S w (root i))
    (hRoots:∀W∈S,∃i∈data.s₂,∃j<data.d,W.1.val 0=(π^j) (root i))
    (Wsel:actualSelectedSegmentIndex data→{W // W∈S})
    (hRoot:∀z,(Wsel z).val.1.val 0=(π^z.2.val.val) (root z.1.1.val)):
    ∀W∈S,∃z,(Wsel z).val=W:=by
  intro W hW
  obtain ⟨i,hi,j,hj,hjroot⟩:=hRoots W hW
  have hspoke:Sum.inr ((π^j) (root i),w)∈markedWheelPhysicalResources W:=by
    apply (markedWheelPhysicalResources_spoke W _ _).mpr
    refine ⟨hHub W hW,?_⟩
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,hjroot⟩
  have hjT:j∈data.T i:=by
    rw [hT i hi]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hj,⟨W,hW,hspoke⟩⟩
  obtain ⟨a,b',hab,haj,hjb⟩:=selected_segment_in_maximal_run data.d (data.T i) (data.hT i) j hjT
  let r:SelectedRunIndex data.s₂ data.d data.T:=⟨⟨i,hi⟩,⟨(a,b'),hab⟩⟩
  let z:actualSelectedSegmentIndex data:=⟨r,⟨⟨j,by omega⟩,haj,hjb⟩⟩
  have hzspoke:Sum.inr ((π^j) (root i),w)∈markedWheelPhysicalResources (Wsel z).val:=by
    apply (markedWheelPhysicalResources_spoke (Wsel z).val _ _).mpr
    refine ⟨hHub _ (Wsel z).property,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨0,Finset.mem_univ _,?_⟩
    simpa [z,r] using hRoot z
  by_cases heq:(Wsel z).val=W
  · exact ⟨z,heq⟩
  · have hdj:=hDis (Wsel z).val (Wsel z).property W hW heq
    exact (Finset.disjoint_left.mp hdj hzspoke hspoke).elim
end Oberwolfach
