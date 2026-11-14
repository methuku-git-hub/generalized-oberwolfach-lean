module

public import Oberwolfach.ActualSourceOrientationProperties

@[expose] public section
/-! The actual source-piece orientation also has at most one outgoing arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_source_orientation_has_unique_outgoing
    {X:Type} [Fintype X] [DecidableEq X]
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces):
    ∀x y z,D x y→D x z→y=z:=by
  classical
  intro x y z hy hz
  obtain ⟨p,hp,hyp⟩:=Finset.mem_biUnion.mp ((hArcs x y).1 hy)
  obtain ⟨q,hq,hzq⟩:=Finset.mem_biUnion.mp ((hArcs x z).1 hz)
  have hp':p∈pieces:=List.mem_toFinset.mp hp
  have hq':q∈pieces:=List.mem_toFinset.mp hq
  rcases prescribed_pairwise_rel_or_eq (fun p q:PrescribedSourcePiece X=>Disjoint p.vertices.toFinset q.vertices.toFinset)
    (fun _ _ h=>h.symm) pieces hpair p hp' q hq' with heq | hdis
  · subst q
    exact prescribed_piece_unique_successor p D ⊥ (prescribed_original_piece_valid p D (hvalid p hp')) x y z hyp hzq
  · have hxp:x∈p.vertices.toFinset:=List.mem_toFinset.mpr (prescribed_source_piece_arc_endpoints p (x,y) hyp).1
    have hxq:x∈q.vertices.toFinset:=List.mem_toFinset.mpr (prescribed_source_piece_arc_endpoints q (x,z) hzq).1
    exact False.elim (Finset.disjoint_left.mp hdis hxp hxq)
end Oberwolfach
