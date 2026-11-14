module

public import Oberwolfach.FactorSourcePieceList
public import Oberwolfach.PrescribedPieceArcPhysical

@[expose] public section
/-! Identify the source-piece graph with the original two-factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_piece_physical_edge_endpoints (p:PrescribedSourcePiece V) (x y:V)
    (he:s(x,y)∈p.edges):x∈p.vertices ∧ y∈p.vertices := by
  rw [prescribed_piece_edges_are_arc_images] at he
  obtain ⟨e,he,hee⟩:=Finset.mem_image.mp he
  rcases e with ⟨a,b⟩
  have hab:=prescribed_source_piece_arc_endpoints p (a,b) he
  have heq:s(a,b)=s(x,y):=hee
  rcases Sym2.eq_iff.mp heq with h|h
  · rcases h with ⟨rfl,rfl⟩;exact hab
  · rcases h with ⟨rfl,rfl⟩;exact ⟨hab.2,hab.1⟩

theorem two_factor_source_pieces_exact (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2):
    ∃ (pieces:List (PrescribedSourcePiece V)),
      (∀ p∈pieces,p.Shape) ∧
      pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀ x,∃ p∈pieces,x∈p.vertices) ∧
      (∀ x y,F.Adj x y ↔ ∃ p∈pieces,s(x,y)∈p.edges) := by
  obtain ⟨pieces,hshape,hdisj,hvertices,hedges⟩:=two_factor_source_piece_list F hF
  refine ⟨pieces,hshape,hdisj,hvertices,?_⟩
  intro x y
  rw [hedges x y]
  constructor
  · rintro ⟨p,hp,hx,he⟩; exact ⟨p,hp,he⟩
  · rintro ⟨p,hp,he⟩
    exact ⟨p,hp,(source_piece_physical_edge_endpoints p x y he).1,he⟩
end Oberwolfach
