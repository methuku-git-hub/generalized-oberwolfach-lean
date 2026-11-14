module

public import Oberwolfach.ActualOldPieceDomain
public import Oberwolfach.ActualOldPiecesAvoidFinal

@[expose] public section
/-! After removing final-path interiors, the old source domain consists of
prescribed anchors and the actual selected runs and cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_domain_without_final_interiors
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed):
    data.oldDomain\data.additionalSelectedInteriors=data.prescribed ∪
      Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset):=by
  classical
  let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
  let D:=data.additionalSelectedInteriors
  have hcycle:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset):=Finset.Subset.antisymm data.hEmbed hCycle
  have hA:A=(Finset.univ.biUnion (fun r:SelectedRunIndex data.s₂ data.d data.T=>(data.path (.inr r)).support.toFinset)) ∪ data.Cembed:=by
    dsimp [A]
    rw [actual_old_piece_domain_eq data,hcycle]
  have hdomain:data.oldDomain=(data.prescribed ∪ A) ∪ D:=by
    rw [hA]
    simp only [ActualResidualData.oldDomain,D,Finset.union_assoc]
  have hDdeleted:D⊆data.deletedVertices:=by
    intro x hx
    apply Finset.mem_union_right
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨.inl i,Finset.mem_univ _,hi⟩
  have hpres:Disjoint data.prescribed D:=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hr: x∈data.remaining:=(data.graph_facts hG).2.1 hx
    exact (Finset.mem_sdiff.mp hr).2 (hDdeleted hy)
  have hAfinal:Disjoint A D:=actual_old_piece_paths_avoid_final_interiors data
  rw [hdomain,Finset.union_sdiff_distrib,Finset.sdiff_self,Finset.union_empty,
    Finset.union_sdiff_distrib,Finset.sdiff_eq_self_of_disjoint hpres,Finset.sdiff_eq_self_of_disjoint hAfinal]
end Oberwolfach
