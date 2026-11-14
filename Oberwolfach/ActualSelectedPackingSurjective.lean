module

public import Oberwolfach.ActualSelectedPackingPositions
public import Oberwolfach.MarkedWheelSpokeLabelsDisjoint

@[expose] public section
/-! Every packed wheel with a selected interval-root label is among the
wheels chosen for the actual maximal runs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_packing_wheels_surjective
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (root:K→V) (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U)
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hT:∀i∈data.s₂,data.T i=packedMarkedPositions tail head ktail khead m b data.d π H₀ Hₖ M hub (root i))
    (haddress:∀Z∈M,Z.2.val=hub ∧ ∃i∈data.s₂,∃j,j<data.d ∧ Z.1.val 0=(π^j) (root i))
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hW:∀z,W z∈M ∧ (W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val)):
    ∀Z∈M,∃z,W z=Z:=by
  intro Z hZ
  obtain ⟨hHub,i,hi,j,hj,hroot⟩:=haddress Z hZ
  have hjT:j∈data.T i:=by
    rw [hT i hi]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,Z,hZ,hHub,hroot⟩
  obtain ⟨a,c,hac,haj,hjc⟩:=selected_segment_in_maximal_run data.d (data.T i) (data.hT i) j hjT
  let run:SelectedRunIndex data.s₂ data.d data.T:=⟨⟨i,hi⟩,⟨(a,c),hac⟩⟩
  let z:actualSelectedSegmentIndex data:=⟨run,⟨⟨j,by omega⟩,haj,hjc⟩⟩
  refine ⟨z,?_⟩
  by_contra hne
  have hd:=hpack (W z) (hW z).1 Z hZ hne
  have hh:(W z).2.val=Z.2.val:=(hW z).2.1.trans hHub.symm
  have hr:(W z).1.val 0=Z.1.val 0:=by
    rw [(hW z).2.2,hroot]
  exact disjoint_marked_wheels_distinct_spoke_labels (W z) Z hd hh 0 0 hr
end Oberwolfach
