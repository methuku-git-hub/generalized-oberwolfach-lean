module

public import Oberwolfach.ResidualDeletedVertexSetIdentity
public import Oberwolfach.ActualSelectedRunMarkers
public import Oberwolfach.ActualParentBufferedMarker

@[expose] public section
/-! Every marker of an approximate path is either prescribed or lies on
one of its actual selected runs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_approx_marker_prescribed_or_selected_run
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (i:K) (hi:i∈data.s₂) (j:ℕ) (hj:j≤data.d):
    (data.P i).getVert (2+data.c*j)∈data.prescribed ∨
      ∃a b,(a,b)∈selectedSegmentRuns data.d (data.T i) ∧ a≤j ∧ j≤b+1:=by
  classical
  by_cases hsurvive:j∈survivingSegmentMarkers data.d (data.T i)
  · left
    let C:=data.t.biUnion (fun j=>(data.C j).support.toFinset)
    have hc:∀i∈data.s₁∪data.s₂,Disjoint (data.P i).support.toFinset C:=by
      intro k hk
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨j,hj,hxj⟩:=Finset.mem_biUnion.mp hy
      exact Finset.disjoint_left.mp (data.hcross k hk j hj) hx hxj
    have hdel:data.deletedVertices=C ∪ (data.s₁∪data.s₂).biUnion
        (pathFamilyLocalDeletion G data.s₁ data.u data.v data.P data.c data.d data.T data.hT):=by
      unfold ActualResidualData.deletedVertices
      have hh:=deleted_path_family_interiors_identity G data.s₁ data.s₂ data.hs data.u data.v data.P data.c data.d data.T data.hT
      dsimp only [ActualResidualData.Z,ActualResidualData.path,ActualResidualData.start,ActualResidualData.finish]
      simpa only [C] using congrArg (fun A=>C ∪ A) hh
    have hnot:= (selected_marker_survives_global_deletion G data.s₁ data.s₂ data.hs data.u data.v data.P data.hp data.hP
      data.c data.d (lt_of_lt_of_le (by decide:0<3) data.hc) data.hlen data.T data.hT C hc i hi j hj).2 hsurvive
    have hremain:(data.P i).getVert (2+data.c*j)∈data.remaining:=by
      unfold ActualResidualData.remaining
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by rw [hdel];exact hnot⟩
    change (data.P i).getVert (2+data.c*j)∈
      (data.s₁.biUnion (fun i=>{(data.P i).getVert 2,(data.P i).getVert (2+data.c*data.d)})) ∪
      (data.remaining ∩ data.s₂.biUnion (fun i=>(Finset.range (data.d+1)).image (fun j=>(data.P i).getVert (2+data.c*j))))
    apply Finset.mem_union_right
    exact Finset.mem_inter.mpr ⟨hremain,Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩⟩⟩
  · right
    by_contra hnone
    apply hsurvive
    apply (surviving_segment_marker_iff_avoids_runs data.d (data.T i) (data.hT i) j).mpr
    refine ⟨hj,?_⟩
    intro a b hab habj
    apply hnone
    exact ⟨a,b,hab,by omega,by omega⟩

theorem actual_all_approx_markers_preserved
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:K→V) (ψ:X→V)
    (hpres:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i))
    (hrun:∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
      ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (root r.1.val)):
    ∀i∈data.s₂,∀j:Fin (data.d+1),ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i):=by
  intro i hi j
  have hmarker:(data.P i).getVert (2+data.c*j.val)=bufferedMarker data.c data.d (ext i) j:=
    actual_parent_buffered_marker data ext hsupp i (Finset.mem_union_right _ hi) j
  rcases actual_approx_marker_prescribed_or_selected_run data i hi j.val (by have hh:=j.isLt;omega) with hp|⟨a,b,hab,haj,hjb⟩
  · apply hpres i j
    rw [←hmarker]
    exact hp
  · let r:SelectedRunIndex data.s₂ data.d data.T:=⟨⟨i,hi⟩,⟨(a,b),hab⟩⟩
    let k:=j.val-a
    have hk:k≤r.2.val.2+1-r.2.val.1:=by dsimp [k,r];omega
    have hj':a+k=j.val:=by dsimp [k];omega
    have hh:=hrun r k hk
    dsimp only [r] at hh
    rw [hj',hmarker] at hh
    exact hh
end Oberwolfach
