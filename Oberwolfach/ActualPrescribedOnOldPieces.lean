module

public import Oberwolfach.ActualOldPieceDomain

@[expose] public section
/-! A prescribed residual vertex lying on an old selected piece is an
endpoint of a selected run; selected cycle vertices are deleted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_old_piece_is_run_endpoint
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (x:X) (hx:x∈data.prescribed)
    (hA:x∈Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)):
    ∃r:SelectedRunIndex data.s₂ data.d data.T,x=data.start (.inr r) ∨ x=data.finish (.inr r):=by
  have hrem:x∈data.remaining:=(data.graph_facts hG).2.1 hx
  have hnot:x∉data.deletedVertices:=(Finset.mem_sdiff.mp hrem).2
  rw [actual_old_piece_domain_eq data] at hA
  rcases Finset.mem_union.mp hA with hp|hc
  · obtain ⟨r,_,hr⟩:=Finset.mem_biUnion.mp hp
    by_cases hs:x=data.start (.inr r)
    · exact ⟨r,Or.inl hs⟩
    by_cases hf:x=data.finish (.inr r)
    · exact ⟨r,Or.inr hf⟩
    · have hd:x∈data.deletedVertices:=by
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨.inr r,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨hr,?_⟩⟩
        simp [hs,hf]
      exact False.elim (hnot hd)
  · have hd:x∈data.deletedVertices:=Finset.mem_union_left _ hc
    exact False.elim (hnot hd)
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_anchor_piece_agreement_from_run_endpoints
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V) (g:{x // x∈data.prescribed}↪V),
    (∀r:SelectedRunIndex data.s₂ data.d data.T,
      ∀(ha:data.start (.inr r)∈A) (hp:data.start (.inr r)∈data.prescribed),
        f ⟨data.start (.inr r),ha⟩=g ⟨data.start (.inr r),hp⟩)→
    (∀r:SelectedRunIndex data.s₂ data.d data.T,
      ∀(ha:data.finish (.inr r)∈A) (hp:data.finish (.inr r)∈data.prescribed),
        f ⟨data.finish (.inr r),ha⟩=g ⟨data.finish (.inr r),hp⟩)→
    ∀x (ha:x∈A) (hp:x∈data.prescribed),f ⟨x,ha⟩=g ⟨x,hp⟩:=by
  intro A f g hs hf x ha hp
  obtain ⟨r,hr|hr⟩:=actual_prescribed_old_piece_is_run_endpoint data hG x hp ha
  · subst x
    exact hs r ha hp
  · subst x
    exact hf r ha hp
end Oberwolfach
