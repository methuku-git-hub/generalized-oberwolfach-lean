module

public import Oberwolfach.ActualOldPiecesAvoidFinal

@[expose] public section
/-! A selected component cycle contributes its entire edge set to the
nonfinal old edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_cycle_edges_old
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (j:{j // j∈data.t}):
    (data.C j.val).edges.toFinset⊆data.deletedEdges\
      (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset)):=by
  intro edge he
  apply Finset.mem_sdiff.mpr
  constructor
  · change edge∈data.t.biUnion (fun j=>(data.C j).edges.toFinset) ∪
      Finset.univ.biUnion (fun z:data.Z=>(data.path z).edges.toFinset)
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j.val,j.property,he⟩)
  · intro hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hf
    have hsub:=deleted_path_support_subset_parent G data.s₁ data.s₂ data.u data.v data.P data.c data.d data.hlen data.T
      (fun i _=>data.hT i) (.inl i)
    have hdis:=data.hcross i.val (Finset.mem_union_left _ i.property) j.val j.property
    induction edge using Sym2.ind with
    | _ x y =>
      have hj:x∈(data.C j.val).support.toFinset:=List.mem_toFinset.mpr ((data.C j.val).fst_mem_support_of_mem_edges (List.mem_toFinset.mp he))
      have hi':x∈(data.path (.inl i)).support.toFinset:=List.mem_toFinset.mpr ((data.path (.inl i)).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hi))
      exact Finset.disjoint_left.mp hdis (hsub hi') hj
end Oberwolfach
