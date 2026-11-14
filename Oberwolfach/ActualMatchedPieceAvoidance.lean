module

public import Oberwolfach.ActualMatchedRunMarkers

@[expose] public section
/-! Transfer avoidance from ordinary-spoke vertices and approximate markers
to every vertex of every actual matched old piece. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_pieces_avoid_reserved_labels
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (π:Equiv.Perm V) (root:K→V) (Ord Y:Finset V)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z))
    (hcycle:∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord)
    (hrun:∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
      ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val))
    (hOrd:Disjoint Ord Y)
    (hwindow:∀i∈data.s₂,∀j:Fin (data.d+1),(π^j.val) (root i)∉Y)
    (ψ:X→V):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    ∀z:actualOldPieceIndex data,∀x∈(actualOldPieceWalk data z).support,ψ x∉Y:=by
  intro A f hψ hf z x hx
  have hxA:x∈A:=Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr hx⟩
  obtain ⟨k,hk,hkle⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  have himage:ψ x=(q z).getVert k:=by
    rw [hψ x hxA]
    have hh:=hf z ⟨k,by omega⟩
    have hmem:(actualOldPieceWalk data z).getVert k∈A:=
      Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support k)⟩
    have heq:(⟨(actualOldPieceWalk data z).getVert k,hmem⟩:{x // x∈A})=⟨x,hxA⟩:=Subtype.ext hk
    rw [heq] at hh
    exact hh
  have ht:ψ x∈(q z).support:=by rw [himage];exact (q z).getVert_mem_support k
  cases z with
  | inl j =>
    exact fun hy=>Finset.disjoint_left.mp hOrd (hcycle j _ ht) hy
  | inr r =>
    by_cases ho:ψ x∈Ord
    · exact fun hy=>Finset.disjoint_left.mp hOrd ho hy
    · obtain ⟨j,_,_,hj⟩:=hrun r _ ht ho
      rw [hj]
      exact hwindow r.1.val r.1.property j
end Oberwolfach
