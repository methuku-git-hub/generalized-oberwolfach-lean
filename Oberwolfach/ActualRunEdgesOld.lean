module

public import Oberwolfach.ActualSelectedRunProperties

@[expose] public section
/-! Each selected-run edge is an old deleted edge and no selected-run edge is
one of the reserved final path edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_run_edges_old
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (r:SelectedRunIndex data.s₂ data.d data.T):
    (data.path (.inr r)).edges.toFinset⊆data.deletedEdges\
      (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset)):=by
  intro edge he
  apply Finset.mem_sdiff.mpr
  constructor
  · change edge∈data.t.biUnion (fun j=>(data.C j).edges.toFinset) ∪
      Finset.univ.biUnion (fun z:data.Z=>(data.path z).edges.toFinset)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨.inr r,Finset.mem_univ _,he⟩)
  · intro hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hf
    have hdis:=deleted_path_family_vertex_disjoint G data.s₁ data.s₂ data.hs data.u data.v data.P data.hp data.hP data.c data.d
      (lt_of_lt_of_le (by decide:0<3) data.hc) data.hlen data.T (fun i _=>data.hT i) (.inr r) (.inl i) (by simp)
    induction edge using Sym2.ind with
    | _ x y =>
      have hr:x∈(data.path (.inr r)).support.toFinset:=List.mem_toFinset.mpr ((data.path (.inr r)).fst_mem_support_of_mem_edges (List.mem_toFinset.mp he))
      have hs:x∈(data.path (.inl i)).support.toFinset:=List.mem_toFinset.mpr ((data.path (.inl i)).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hi))
      exact Finset.disjoint_left.mp hdis hr hs
end Oberwolfach
