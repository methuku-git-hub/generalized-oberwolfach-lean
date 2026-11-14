module

public import Oberwolfach.ActualOldPieceTargetMatching
public import Oberwolfach.ActualOldEmbeddingBuffered

@[expose] public section
/-! Match the fixed actual old pieces first; then every compatible prescribed
anchor map extends the same partial map to the exact buffered old domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_matched_embedding_on_buffered_complement
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Nonempty V] [DecidableEq K] [DecidableEq J] [Fintype I]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (b:I≃{i // i∈data.s₁})
    (ext:∀i:I,Fin (data.c*data.d+5)↪X) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i))
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V)
    (q:∀z,H.Walk (u z) (v z)) (hq:∀z,(q z).IsPath)
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hqdis:∀z w,z≠w→Disjoint (q z).support.toFinset (q w).support.toFinset):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∃f:{x // x∈A}↪V,
      (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
        f ⟨(actualOldPieceWalk data z).getVert k.val,
          Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
          (q z).getVert k.val) ∧
      ∀g:{x // x∈data.prescribed}↪V,
        (∀x (hx:x∈A) (hy:x∈data.prescribed),f ⟨x,hx⟩=g ⟨x,hy⟩)→
        (∀x (hx:x∈data.prescribed) (hxa:x∉A) (y:{x // x∈A}),g ⟨x,hx⟩≠f y)→
        ∃ψ:X→V,Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
          (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩) ∧
          (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩):=by
  classical
  intro A
  obtain ⟨f,hf⟩:=actual_old_pieces_match_target_walks data H u v q hq hlen hqdis
  refine ⟨f,hf,?_⟩
  intro g hagree hcross
  exact actual_old_embedding_from_pieces_and_anchors_buffered data hG hCycle b ext inner hinner hsupp f g hagree hcross
end Oberwolfach
