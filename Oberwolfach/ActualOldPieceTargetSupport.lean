module

public import Oberwolfach.ActualOldDomainSplit
public import Oberwolfach.SimpleWalkVertexSequence

@[expose] public section
/-! Every vertex of a selected target path is the image of an old source
vertex outside the final path interiors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_piece_target_support_in_old_image
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z))
    (hq:∀z,(q z).IsPath) (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (f:{x // x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))}↪V)
    (ψ:X→V)
    (hψf:∀x (hx:x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))),ψ x=f ⟨x,hx⟩)
    (hf:∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=(q z).getVert k.val):
    ∀z,(q z).support.toFinset⊆(data.oldDomain\data.additionalSelectedInteriors).image ψ:=by
  intro z y hy
  rw [←simple_walk_vertex_embedding_support (SimpleGraph.completeGraph V) (q z) (hq z)] at hy
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hy
  have hk:i.val<(actualOldPieceWalk data z).length+1:=by rw [←hlen z];exact i.isLt
  let k:Fin ((actualOldPieceWalk data z).length+1):=⟨i.val,hk⟩
  let x: X:=(actualOldPieceWalk data z).getVert k.val
  have hx:x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)):=
    Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩
  have hxold:x∈data.oldDomain\data.additionalSelectedInteriors:=by
    rw [actual_old_domain_without_final_interiors data hG hCycle]
    exact Finset.mem_union_right _ hx
  apply Finset.mem_image.mpr
  refine ⟨x,hxold,?_⟩
  rw [hψf x hx]
  have hh:=hf z k
  change f ⟨x,hx⟩=(q z).getVert i.val at hh
  exact hh.trans hi
end Oberwolfach
