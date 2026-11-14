module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage

@[expose] public section

/-! When no first-family paths remain, every endpoint of a deleted old
edge belongs to the old embedding domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deleted_edges_endpoints_in_old_domain
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (hfirst:data.s₁=∅)
    (hcycles:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (e:Sym2 X) (he:e∈data.deletedEdges) (x:X) (hx:x∈e):x∈data.oldDomain :=by
  change e∈data.t.biUnion (fun j=>(data.C j).edges.toFinset) ∪
    Finset.univ.biUnion (fun z:data.Z=>(data.path z).edges.toFinset) at he
  rcases Finset.mem_union.mp he with hc|hp
  · obtain ⟨j,hj,he⟩:=Finset.mem_biUnion.mp hc
    have hxC:x∈(data.C j).support.toFinset:=
      List.mem_toFinset.mpr ((data.C j).mem_support_of_mem_edges (List.mem_toFinset.mp he) hx)
    have hxembed:x∈data.Cembed:=hcycles (Finset.mem_biUnion.mpr ⟨j,hj,hxC⟩)
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hxembed)
  · obtain ⟨z,_,he⟩:=Finset.mem_biUnion.mp hp
    cases z with
    | inl i =>
      have hi:=i.property
      simp [hfirst] at hi
    | inr r =>
      have hxr:x∈(data.path (.inr r)).support.toFinset:=
        List.mem_toFinset.mpr ((data.path (.inr r)).mem_support_of_mem_edges (List.mem_toFinset.mp he) hx)
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,hxr⟩)))
end Oberwolfach
