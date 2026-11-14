module

public import Oberwolfach.ActualOldDomainSplit
public import Oberwolfach.ActualFinalInteriorIdentification
public import Oberwolfach.ActualPrescribedBufferedMarkers
public import Oberwolfach.ActualMatchedPieceAvoidance

@[expose] public section
/-! The actual old image avoids any list avoiding ordinary spokes and every
interval label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_old_image_avoids_list
    {X V K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype I]
    {G:SimpleGraph X} (hG:G.IsRegularOfDegree 2) (data:ActualResidualData (K:=K) (J:=J) G)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (b:I≃{i // i∈data.s₁}) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i k,inner i k=ext (b i).val ⟨k.val+2,by omega⟩)
    (π:Equiv.Perm V) (root:K→V) (Ord L:Finset V)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z))
    (hcycle:∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord)
    (hrun:∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
      ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val))
    (hOrd:Disjoint Ord L) (hlabels:∀i (j:Fin (data.d+1)),(π^j.val) (root i)∉L)
    (ψ:X→V)
    (hpres:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i)):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩)→
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ) L:=by
  intro A f hψ hf
  have hpiece:=actual_matched_pieces_avoid_reserved_labels data π root Ord L H u v q hcycle hrun hOrd
    (fun i _ j=>hlabels i j) ψ f hψ hf
  have heq:=actual_final_interiors_eq_buffered_strict data b (fun i=>ext (b i).val) inner hinner
    (fun i=>hsupp (b i).val (Finset.mem_union_left _ (b i).property))
  have hold:=actual_old_domain_without_final_interiors data hG hCycle
  apply Finset.disjoint_left.mpr
  intro y hy hL
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
  have hx':x∈data.prescribed ∪ A:=by
    rw [←hold,heq]
    exact hx
  rcases Finset.mem_union.mp hx' with hp|hp
  · obtain ⟨⟨i,j⟩,_,hi⟩:=Finset.mem_image.mp (actual_prescribed_subset_buffered_markers data ext hsupp hp)
    subst x
    rw [hpres i j hp] at hL
    exact hlabels i j hL
  · obtain ⟨z,_,hz⟩:=Finset.mem_biUnion.mp hp
    exact hpiece z x (List.mem_toFinset.mp hz) hL
end Oberwolfach
