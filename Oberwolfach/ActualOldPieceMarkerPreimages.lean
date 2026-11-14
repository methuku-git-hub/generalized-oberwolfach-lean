module

public import Oberwolfach.ActualMatchedRunMarkers
public import Oberwolfach.ActualParentBufferedMarker

@[expose] public section
/-! Trace every nonordinary target label of the matched old pieces to the
corresponding actual source marker. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_piece_nonordinary_marker_preimages
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:K→V) (Ord:Finset V)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V) (q:∀z,H.Walk (u z) (v z))
    (hcycle:∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord)
    (hrun:∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
      ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val))
    (hmarks:∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
      (q (.inr r)).getVert (data.c*j)=(π^(r.2.val.1+j)) (root r.1.val)):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V),
    (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
        (q z).getVert k.val)→
    ∀y:{x // x∈A},f y∉Ord→
      ∃(i:K) (j:Fin (data.d+1)) (hm:bufferedMarker data.c data.d (ext i) j∈A),
        f y=(π^j.val) (root i) ∧ f ⟨bufferedMarker data.c data.d (ext i) j,hm⟩=(π^j.val) (root i):=by
  classical
  intro A f hf y hnot
  obtain ⟨z,_,hy⟩:=Finset.mem_biUnion.mp y.property
  obtain ⟨k,hk,hkle⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hy)
  have hfy:f y=(q z).getVert k:=by
    have hh:=hf z ⟨k,by omega⟩
    have hmem:(actualOldPieceWalk data z).getVert k∈A:=
      Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support k)⟩
    have heq:(⟨(actualOldPieceWalk data z).getVert k,hmem⟩:{x // x∈A})=y:=Subtype.ext hk
    rw [heq] at hh
    exact hh
  have hyq:f y∈(q z).support:=by rw [hfy];exact (q z).getVert_mem_support k
  cases z with
  | inl t =>exact False.elim (hnot (hcycle t _ hyq))
  | inr r =>
    obtain ⟨j,hlo,hhi,hlabel⟩:=hrun r _ hyq hnot
    let a:=j.val-r.2.val.1
    have ha:a≤r.2.val.2+1-r.2.val.1:=by dsimp [a];omega
    have hj:r.2.val.1+a=j.val:=by dsimp [a];omega
    have hlen:(data.path (.inr r)).length=data.c*(r.2.val.2+1-r.2.val.1):=by
      exact (deleted_path_lengths G data.s₁ data.s₂ data.u data.v data.P data.hp data.c data.d
        (lt_of_lt_of_le (by decide:0<3) data.hc) data.hlen data.T (fun i _=>data.hT i)).2 r.1 r.2
    have hbound:data.c*a≤(data.path (.inr r)).length:=by
      rw [hlen]
      exact Nat.mul_le_mul_left data.c ha
    have hmarker:(data.path (.inr r)).getVert (data.c*a)=bufferedMarker data.c data.d (ext r.1.val) j:=by
      rw [actual_selected_run_marker_getVert data r a ha,hj]
      exact actual_parent_buffered_marker data ext hsupp r.1.val (Finset.mem_union_right _ r.1.property) j
    have hm:bufferedMarker data.c data.d (ext r.1.val) j∈A:=by
      rw [←hmarker]
      exact Finset.mem_biUnion.mpr ⟨.inr r,Finset.mem_univ _,List.mem_toFinset.mpr ((data.path (.inr r)).getVert_mem_support _)⟩
    have hfmark:f ⟨bufferedMarker data.c data.d (ext r.1.val) j,hm⟩=(π^j.val) (root r.1.val):=by
      have hh:=hf (.inr r) ⟨data.c*a,by change data.c*a<(data.path (.inr r)).length+1;omega⟩
      change f ⟨(data.path (.inr r)).getVert (data.c*a),_⟩=(q (.inr r)).getVert (data.c*a) at hh
      have hmem:(data.path (.inr r)).getVert (data.c*a)∈A:=by
        rw [hmarker];exact hm
      have heq:(⟨(data.path (.inr r)).getVert (data.c*a),hmem⟩:{x // x∈A})=
          ⟨bufferedMarker data.c data.d (ext r.1.val) j,hm⟩:=Subtype.ext hmarker
      rw [heq] at hh
      exact hh.trans (by simpa only [hj] using hmarks r a ha)
    exact ⟨r.1.val,j,hm,hlabel,hfmark⟩
end Oberwolfach
