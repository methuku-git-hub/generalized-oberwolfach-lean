module

public import Oberwolfach.ActualApproxMarkerCoverage
public import Oberwolfach.ActualOldDomainSplit

@[expose] public section
/-! The actual buffered old embedding contains every extended approximate
interval, not merely the prescribed anchors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_approx_intervals_occupied
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:K→V) (ψ:X→V)
    (hpres:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i))
    (hrun:∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
      ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (root r.1.val)):
    ∀i∈data.s₂,∀j:Fin (data.d+1),
      ∃x∈data.oldDomain\data.additionalSelectedInteriors,ψ x=(π^j.val) (root i):=by
  intro i hi j
  let x:=bufferedMarker data.c data.d (ext i) j
  have hx:(data.P i).getVert (2+data.c*j.val)=x:=
    actual_parent_buffered_marker data ext hsupp i (Finset.mem_union_right _ hi) j
  have hmem:x∈data.prescribed ∪ Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset):=by
    rcases actual_approx_marker_prescribed_or_selected_run data i hi j.val (by have hh:=j.isLt;omega) with hp|⟨a,b,hab,haj,hjb⟩
    · apply Finset.mem_union_left
      rw [←hx]
      exact hp
    · apply Finset.mem_union_right
      let r:SelectedRunIndex data.s₂ data.d data.T:=⟨⟨i,hi⟩,⟨(a,b),hab⟩⟩
      let k:=j.val-a
      have hk:k≤r.2.val.2+1-r.2.val.1:=by dsimp [k,r];omega
      have hj':a+k=j.val:=by dsimp [k];omega
      have hh: (data.path (.inr r)).getVert (data.c*k)=x:=by
        rw [actual_selected_run_marker_getVert data r k hk]
        dsimp only [r]
        rw [hj',hx]
      apply Finset.mem_biUnion.mpr
      refine ⟨.inr r,Finset.mem_univ _,?_⟩
      change x∈(data.path (.inr r)).support.toFinset
      rw [←hh]
      exact List.mem_toFinset.mpr ((data.path (.inr r)).getVert_mem_support _)
  have hold:x∈data.oldDomain\data.additionalSelectedInteriors:=by
    rw [actual_old_domain_without_final_interiors data hG hCycle]
    exact hmem
  exact ⟨x,hold,actual_all_approx_markers_preserved data ext hsupp π root ψ hpres hrun i hi j⟩
end Oberwolfach
