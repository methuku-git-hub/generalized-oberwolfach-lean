module

public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.MarkedReferenceAbsorberDeletion

@[expose] public section
/-! If a wheel packing decomposes the reserved resources, the graphs formed
from the resource set agree exactly with its physical rim and spoke graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_reserved_graphs_of_packing
    (C:Finset (Finset V⊕(V×U))) (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hC:M.biUnion markedWheelPhysicalResources=C):
    markedPackingRimGraph M=physicalEdgeGraph (markedReservedRimPairs C) ∧
    markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)=markedFiniteSpokeGraph (markedReservedSpokePairs C):=by
  constructor
  · ext x y
    change (x≠y∧({x,y}:Finset V)∈markedPackingRims M)↔_
    rw [(marked_reserved_resource_graphs C).1,←hC,markedPackingResources_rim]
  · ext x y
    cases x with
    | inl v=>cases y with
      | inl w=>simp only [(markedFiniteSpokeGraph_same_part _).1]
      | inr u=>
        rw [markedFiniteSpokeGraph_adj,(marked_reserved_resource_graphs C).2.1,←hC]
        simp only [Finset.mem_biUnion,markedWheelSpokePairs,Finset.mem_image,Finset.mem_univ,true_and,
          Prod.mk.injEq,markedWheelPhysicalResources_spoke,markedWheelRows]
        aesop
    | inr u=>cases y with
      | inl v=>
        rw [SimpleGraph.adj_comm (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)),
          SimpleGraph.adj_comm (markedFiniteSpokeGraph (markedReservedSpokePairs C))]
        rw [markedFiniteSpokeGraph_adj,(marked_reserved_resource_graphs C).2.1,←hC]
        simp only [Finset.mem_biUnion,markedWheelSpokePairs,Finset.mem_image,Finset.mem_univ,true_and,
          Prod.mk.injEq,markedWheelPhysicalResources_spoke,markedWheelRows]
        aesop
      | inr z=>simp only [(markedFiniteSpokeGraph_same_part _).2]
end Oberwolfach
