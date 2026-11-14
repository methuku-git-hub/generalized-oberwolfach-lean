module

public import Oberwolfach.ResidualPathPiecesWithArcs
public import Oberwolfach.PrescribedFamilyArcUniqueness
public import Oberwolfach.PrescribedOriginalSourcePieces
public import Oberwolfach.PrescribedPieceArcPhysical

@[expose] public section
/-! The fixed source-piece orientation covers each physical factor edge and
has at most one incoming arc at every source vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_source_orientation_covers_and_has_unique_incoming
    {X:Type} [Fintype X] [DecidableEq X] (G:SimpleGraph X)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hEdges:sourcePieceEdgesUnion pieces=G.edgeFinset)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces):
    (∀x y,G.Adj x y→D x y ∨ D y x) ∧
      (∀x y z,D y x→D z x→y=z):=by
  classical
  constructor
  · intro x y hxy
    have he:s(x,y)∈sourcePieceEdgesUnion pieces:=by
      rw [hEdges]
      exact SimpleGraph.mem_edgeFinset.mpr hxy
    obtain ⟨p,hp,he⟩:=Finset.mem_biUnion.mp he
    rw [prescribed_piece_edges_are_arc_images] at he
    obtain ⟨arc,harc,heq⟩:=Finset.mem_image.mp he
    rcases arc with ⟨u,v⟩
    change s(u,v)=s(x,y) at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · left
      apply (hArcs _ _).2
      exact Finset.mem_biUnion.mpr ⟨p,hp,harc⟩
    · right
      apply (hArcs _ _).2
      exact Finset.mem_biUnion.mpr ⟨p,hp,harc⟩
  · intro x y z hy hz
    obtain ⟨p,hp,hyp⟩:=Finset.mem_biUnion.mp ((hArcs y x).1 hy)
    obtain ⟨q,hq,hzq⟩:=Finset.mem_biUnion.mp ((hArcs z x).1 hz)
    have hp':p∈pieces:=List.mem_toFinset.mp hp
    have hq':q∈pieces:=List.mem_toFinset.mp hq
    rcases prescribed_pairwise_rel_or_eq (fun p q:PrescribedSourcePiece X=>Disjoint p.vertices.toFinset q.vertices.toFinset)
      (fun _ _ h=>h.symm) pieces hpair p hp' q hq' with heq | hdis
    · subst q
      exact prescribed_piece_unique_predecessor p D ⊥ (prescribed_original_piece_valid p D (hvalid p hp')) x y z hyp hzq
    · have hxp:x∈p.vertices.toFinset:=List.mem_toFinset.mpr (prescribed_source_piece_arc_endpoints p (y,x) hyp).2
      have hxq:x∈q.vertices.toFinset:=List.mem_toFinset.mpr (prescribed_source_piece_arc_endpoints q (z,x) hzq).2
      exact False.elim (Finset.disjoint_left.mp hdis hxp hxq)
end Oberwolfach
