module

public import Oberwolfach.ActualSelectedSegmentWheelMatching

@[expose] public section
/-! The manuscript's selected-position set is defined by the marked spokes
actually covered by the original physical packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def packedMarkedPositions
    {V U E L:Type} [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:L→V) (m b d:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U) (a:V):Finset ℕ:=
  (Finset.range d).filter (fun j=>∃W∈M,W.2.val=hub ∧ W.1.val 0=(π^j) a)

theorem packed_marked_positions_subset_range
    {V U E L:Type} [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:L→V) (m b d:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U) (a:V):
    packedMarkedPositions tail head ktail khead m b d π H₀ Hₖ M hub a⊆Finset.range d:=by
  exact Finset.filter_subset _ _

theorem actual_selected_segments_choose_wheels_from_packing_positions
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U)
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hT:∀i∈data.s₂,data.T i=packedMarkedPositions tail head ktail khead m b data.d π H₀ Hₖ M hub (root i)):
    ∃W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      (∀z,W z∈M ∧ (W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val)) ∧
      (∀z z',z≠z'→Disjoint (markedWheelPhysicalResources (W z)) (markedWheelPhysicalResources (W z'))):=by
  classical
  apply actual_selected_segments_choose_packed_wheels data tail head ktail khead m b π H₀ Hₖ root hinj hdis M hub hpack
  intro z
  have hr:=(selected_run_mem data.d (data.T z.1.1.val) (data.hT z.1.1.val) z.1.2.val.1 z.1.2.val.2).mp z.1.2.property
  have hj:z.2.val.val∈data.T z.1.1.val:=hr.2.1 z.2.val.val z.2.property.1 z.2.property.2
  have hsub:data.T z.1.1.val⊆packedMarkedPositions tail head ktail khead m b data.d π H₀ Hₖ M hub (root z.1.1.val):=
    (hT z.1.1.val z.1.1.property).subset
  exact (Finset.mem_filter.mp (hsub hj)).2
end Oberwolfach
