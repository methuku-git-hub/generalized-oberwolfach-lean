module

public import Oberwolfach.FactorPieceGraphIdentity
public import Oberwolfach.PrescribedPieceSourceModel

@[expose] public section
/-! The source graph and source vertex set constructed from the pieces are
exactly the original graph and its full vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_piece_model_exact (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2):
    ∃ (pieces:List (PrescribedSourcePiece V)),
      (∀ p∈pieces,p.Shape) ∧
      pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      let ps:=pieces.map (fun p=>((),p));
      prescribedSourceVertices ps ()=Finset.univ ∧ prescribedSourceGraph ps ()=F := by
  obtain ⟨pieces,hshape,hdisj,hvertices,hedges⟩:=two_factor_source_pieces_exact F hF
  refine ⟨pieces,hshape,hdisj,?_,?_⟩
  · ext x
    simp only [Finset.mem_univ,iff_true,prescribed_source_model_vertices]
    obtain ⟨p,hp,hx⟩:=hvertices x
    refine ⟨((),p),?_,trivial,hx⟩
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  · ext x y
    rw [prescribedSourceGraph,SimpleGraph.fromEdgeSet_adj]
    change ((∃ p∈pieces.map (fun p=>((),p)),p.1=() ∧ s(x,y)∈p.2.edges) ∧ x≠y) ↔ F.Adj x y
    constructor
    · rintro ⟨⟨p,hp,_,he⟩,hxy⟩
      obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
      exact (hedges x y).2 ⟨q,hq,he⟩
    · intro hxy
      obtain ⟨p,hp,he⟩:=(hedges x y).1 hxy
      refine ⟨⟨((),p),List.mem_map.mpr ⟨p,hp,rfl⟩,rfl,he⟩,hxy.ne⟩
end Oberwolfach
