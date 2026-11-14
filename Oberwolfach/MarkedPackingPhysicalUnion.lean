module

public import Oberwolfach.MarkedPackingUnions
public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! The union of the two actually constructed packings retains physical
edge-disjointness and has precisely the union of their physical graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_packing_union_is_matching
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hN:∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hMN:Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)):
    ∀ W∈M∪N,∀ Z∈M∪N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z):=by
  intro W hW Z hZ hne
  rcases Finset.mem_union.mp hW with hW|hW <;> rcases Finset.mem_union.mp hZ with hZ|hZ
  · exact hM W hW Z hZ hne
  · exact hMN.mono (resource_subset_union _ M W hW) (resource_subset_union _ N Z hZ)
  · exact hMN.symm.mono (resource_subset_union _ N W hW) (resource_subset_union _ M Z hZ)
  · exact hN W hW Z hZ hne

theorem markedPackingPhysicalGraph_union
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    ordinaryPhysicalGraph (markedPackingRimGraph (M∪N)) (markedPackingSpokes (M∪N))=
      ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)⊔
      ordinaryPhysicalGraph (markedPackingRimGraph N) (markedPackingSpokes N):=by
  ext x y
  rcases x with x|u <;> rcases y with y|v
  all_goals simp only [ordinaryPhysicalGraph,SimpleGraph.sup_adj,markedPackingRimGraph_union,
    markedPackingSpokes_union]
  all_goals tauto
end Oberwolfach
