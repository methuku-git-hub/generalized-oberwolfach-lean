module

public import Oberwolfach.PrescribedSourceOriented
public import Oberwolfach.PrescribedSourceRepresentation
public import Oberwolfach.PrescribedPieceSourceModel

@[expose] public section
/-! The original directed path-and-cycle source model is oriented, and its
underlying graph has exactly the physical images of the directed arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X:Type} [Fintype X] [DecidableEq I] [DecidableEq X]

theorem prescribed_source_model_oriented (ps:List (I×PrescribedSourcePiece X))
    (hshape:∀ p∈ps,p.2.Shape) (hapart:ps.Pairwise PrescribedPiecesApart):
    ∀ i x y,prescribedSourceDigraph ps i x y→¬prescribedSourceDigraph ps i y x := by
  intro i x y hxy hyx
  obtain ⟨p,hp,hpi,hpa⟩:=hxy
  obtain ⟨q,hq,hqi,hqa⟩:=hyx
  have heq:p=q:=by
    rcases prescribed_pairwise_rel_or_eq PrescribedPiecesApart prescribed_pieces_apart_symmetric ps hapart p hp q hq with heq|hdis
    · exact heq
    · rcases hdis with hne|hdis
      · exact (hne (hpi.trans hqi.symm)).elim
      · have hpx:x∈p.2.vertices:=(prescribed_source_piece_arc_endpoints p.2 (x,y) hpa).1
        have hqx:x∈q.2.vertices:=(prescribed_source_piece_arc_endpoints q.2 (y,x) hqa).2
        exact ((Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hpx)) (List.mem_toFinset.mpr hqx)).elim
  subst q
  exact prescribed_piece_no_reverse p.2 (hshape p hp) x y hpa hqa

theorem prescribed_source_model_representation (ps:List (I×PrescribedSourcePiece X)):
    ∀ i x y,(prescribedSourceGraph ps i).Adj x y→
      prescribedSourceDigraph ps i x y ∨ prescribedSourceDigraph ps i y x := by
  intro i x y hxy
  have he:s(x,y)∈(prescribedSourceGraph ps i).edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hxy
  obtain ⟨p,hp,hpi,hpE⟩:=prescribed_source_model_edges ps i _ he
  rw [prescribed_piece_edges_are_arc_images] at hpE
  obtain ⟨e,he,hphys⟩:=Finset.mem_image.mp hpE
  rcases e with ⟨u,v⟩
  have ha:prescribedSourceDigraph ps i u v:=⟨p,hp,hpi,he⟩
  change s(u,v)=s(x,y) at hphys
  rcases Sym2.eq_iff.mp hphys with ⟨hu,hv⟩|⟨hu,hv⟩
  · subst u;subst v;exact Or.inl ha
  · subst u;subst v;exact Or.inr ha

theorem prescribed_source_model_degree [Fintype I] (ps:List (I×PrescribedSourcePiece X))
    (hshape:∀ p∈ps,p.2.Shape) (hapart:ps.Pairwise PrescribedPiecesApart):
    ∀ i x,(prescribedSourceGraph ps i).degree x≤2 := by
  apply prescribed_source_degree_from_components (prescribedSourceGraph ps) (prescribedSourceDigraph ps) (fun _=>⊥) ps
    ?_ hapart (prescribed_source_model_arc_graph ps hshape) (prescribed_source_model_edges ps) ?_
  · intro p hp
    exact prescribed_original_piece_valid p.2 (prescribedSourceDigraph ps p.1)
      (prescribed_source_model_piece_valid ps hshape p hp)
  · intro i x y h
    exact h
end Oberwolfach
