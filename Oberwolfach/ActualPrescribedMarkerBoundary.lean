module

public import Oberwolfach.ActualApproxMarkerCoverage
public import Oberwolfach.ResidualGlobalMarkerSet

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_marker_boundary
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (x:X) (hx:x∈data.prescribed):
    (∃i∈data.s₁, x=(data.P i).getVert 2 ∨ x=(data.P i).getVert (2+data.c*data.d)) ∨
    ∃i∈data.s₂, ∃j:ℕ,j≤data.d ∧ x=(data.P i).getVert (2+data.c*j) ∧
      (j=0 ∨ j=data.d ∨ j∉data.T i ∨ j-1∉data.T i):=by
  classical
  let C:=data.t.biUnion (fun j=>(data.C j).support.toFinset)
  have hc:∀i∈data.s₁∪data.s₂,Disjoint (data.P i).support.toFinset C:=by
    intro k hk
    apply Finset.disjoint_left.mpr
    intro y hy hz
    obtain ⟨j,hj,hyj⟩:=Finset.mem_biUnion.mp hz
    exact Finset.disjoint_left.mp (data.hcross k hk j hj) hy hyj
  have hdel:data.deletedVertices=C ∪ (data.s₁∪data.s₂).biUnion
      (pathFamilyLocalDeletion G data.s₁ data.u data.v data.P data.c data.d data.T data.hT):=by
    unfold ActualResidualData.deletedVertices
    have hh:=deleted_path_family_interiors_identity G data.s₁ data.s₂ data.hs data.u data.v data.P data.c data.d data.T data.hT
    dsimp only [ActualResidualData.Z,ActualResidualData.path,ActualResidualData.start,ActualResidualData.finish]
    simpa only [C] using congrArg (fun A=>C ∪ A) hh
  change x∈(data.s₁.biUnion (fun i=>{(data.P i).getVert 2,(data.P i).getVert (2+data.c*data.d)})) ∪
    (data.remaining ∩ data.s₂.biUnion (fun i=>(Finset.range (data.d+1)).image (fun j=>(data.P i).getVert (2+data.c*j)))) at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    exact Or.inl ⟨i,hi,by simpa only [Finset.mem_insert,Finset.mem_singleton] using hx⟩
  · obtain ⟨hrem,hx⟩:=Finset.mem_inter.mp hx
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨j,hj,hx⟩:=Finset.mem_image.mp hx
    have hjd:j≤data.d:=by have hh:=Finset.mem_range.mp hj; omega
    have hnot:x∉C ∪ (data.s₁∪data.s₂).biUnion
        (pathFamilyLocalDeletion G data.s₁ data.u data.v data.P data.c data.d data.T data.hT):=by
      have hh: x∉data.deletedVertices:=(Finset.mem_sdiff.mp hrem).2
      simpa only [hdel] using hh
    have hsurvive:= (selected_marker_survives_global_deletion G data.s₁ data.s₂ data.hs data.u data.v data.P data.hp data.hP
      data.c data.d (by have hh:=data.hc;omega) data.hlen data.T data.hT C hc i hi j hjd).1 (by simpa [←hx] using hnot)
    have hs':j<data.d+1 ∧ ¬(j∈data.T i ∧ 0<j ∧ j-1∈data.T i):=by
      simpa only [survivingSegmentMarkers,Finset.mem_sdiff,Finset.mem_range,Finset.mem_filter] using hsurvive
    have hn:=hs'.2
    refine Or.inr ⟨i,hi,j,hjd,hx.symm,?_⟩
    by_cases h0:j=0
    · exact Or.inl h0
    by_cases hd:j=data.d
    · exact Or.inr (Or.inl hd)
    by_cases hjT:j∈data.T i
    · right;right;right
      intro hjprev
      exact hn ⟨hjT,by omega,hjprev⟩
    · exact Or.inr (Or.inr (Or.inl hjT))
end Oberwolfach
