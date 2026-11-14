module

public import Oberwolfach.ActualOldEmbeddingFromAnchors
public import Oberwolfach.ActualFinalInteriorIdentification

@[expose] public section
/-! Glue the actual old-piece map to the prescribed anchor map on precisely
the old domain outside the final-path interiors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_embedding_from_pieces_and_anchors_buffered
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Nonempty V] [DecidableEq K] [DecidableEq J] [Fintype I]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (b:I≃{i // i∈data.s₁})
    (ext:∀i:I,Fin (data.c*data.d+5)↪X) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i)):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∀(f:{x // x∈A}↪V) (g:{x // x∈data.prescribed}↪V),
    (∀x (hx:x∈A) (hy:x∈data.prescribed),f ⟨x,hx⟩=g ⟨x,hy⟩)→
    (∀x (hx:x∈data.prescribed) (hxa:x∉A) (y:{x // x∈A}),g ⟨x,hx⟩≠f y)→
    ∃ψ:X→V,Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
      (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩) ∧
      (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩):=by
  intro A f g hagree hcross
  obtain ⟨ψ,hinj,hpiece,hpres⟩:=actual_old_embedding_from_pieces_and_anchors data hG hCycle f g hagree hcross
  have hD:=actual_final_interiors_eq_buffered_strict data b ext inner hinner hsupp
  refine ⟨ψ,?_,hpiece,hpres⟩
  rw [←hD]
  exact hinj
end Oberwolfach
