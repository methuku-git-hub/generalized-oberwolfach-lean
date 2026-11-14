module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! The edges deleted from a factor are edges of its previously embedded
path and cycle pieces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
  {F:SimpleGraph X}
namespace ActualResidualData
variable (a:ActualResidualData (K:=K) (J:=J) F)

theorem path_support_in_old_domain (z:a.Z) (x:X) (hx:x∈(a.path z).support.toFinset):
    x∈a.oldDomain :=by
  cases z with
  | inr r =>
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,hx⟩)))
  | inl i =>
    by_cases hs:x=a.start (.inl i)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i.1,i.2,?_⟩
      simp only [start,deletedPathStart] at hs
      simp [hs]
    · by_cases ht:x=a.finish (.inl i)
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i.1,i.2,?_⟩
        simp only [finish,deletedPathEnd] at ht
        simp [ht]
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨hx,?_⟩⟩
        simp [hs,ht]

theorem deleted_edges_subset_factor: a.deletedEdges⊆F.edgeFinset:=by
  intro e he
  apply SimpleGraph.mem_edgeFinset.mpr
  obtain hcycle|hpath:=Finset.mem_union.mp he
  · obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hcycle
    exact (a.C j).edges_subset_edgeSet (List.mem_toFinset.mp hj)
  · obtain ⟨z,_,hz⟩:=Finset.mem_biUnion.mp hpath
    exact (a.path z).edges_subset_edgeSet (List.mem_toFinset.mp hz)

theorem deleted_edge_vertices_in_old_domain
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed):
    ∀e∈a.deletedEdges,∀x∈e.toFinset,x∈a.oldDomain :=by
  intro e he x hx
  obtain hcycle|hpath:=Finset.mem_union.mp he
  · obtain ⟨j,hj,he⟩:=Finset.mem_biUnion.mp hcycle
    have hs:x∈(a.C j).support.toFinset:=by
      apply List.mem_toFinset.mpr
      apply (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).2
      right
      refine ⟨e,List.mem_toFinset.mp he,?_⟩
      simpa only [Sym2.mem_toFinset] using hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (hCycle (Finset.mem_biUnion.mpr ⟨j,hj,hs⟩)))
  · obtain ⟨z,_,he⟩:=Finset.mem_biUnion.mp hpath
    apply a.path_support_in_old_domain z x
    apply List.mem_toFinset.mpr
    apply (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).2
    right
    refine ⟨e,List.mem_toFinset.mp he,?_⟩
    simpa only [Sym2.mem_toFinset] using hx
end ActualResidualData
end Oberwolfach
