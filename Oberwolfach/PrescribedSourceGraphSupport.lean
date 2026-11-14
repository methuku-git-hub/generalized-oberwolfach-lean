module

public import Oberwolfach.PrescribedPieceSourceModel

@[expose] public section
/-! Every endpoint of a source physical edge is a vertex of its listed
source piece. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X:Type} [Fintype X] [DecidableEq I] [DecidableEq X]

theorem prescribed_source_piece_edge_endpoints (p:PrescribedSourcePiece X) (e:Sym2 X)
    (he:e∈p.edges):∀ x∈e.toFinset,x∈p.vertices := by
  rw [prescribed_piece_edges_are_arc_images] at he
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
  rcases a with ⟨u,v⟩
  have hh:=prescribed_source_piece_arc_endpoints p (u,v) ha
  intro x hx
  simp only [prescribedArcPhysical,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact hh.1
  · exact hh.2

theorem prescribed_source_graph_endpoint (ps:List (I×PrescribedSourcePiece X)) (i:I) (x y:X)
    (hxy:(prescribedSourceGraph ps i).Adj x y):x∈prescribedSourceVertices ps i := by
  have he:s(x,y)∈(prescribedSourceGraph ps i).edgeFinset:=SimpleGraph.mem_edgeFinset.mpr hxy
  obtain ⟨p,hp,hpi,hpe⟩:=prescribed_source_model_edges ps i s(x,y) he
  apply (prescribed_source_model_vertices ps i x).mpr
  refine ⟨p,hp,hpi,?_⟩
  exact prescribed_source_piece_edge_endpoints p.2 s(x,y) hpe x (by simp [Sym2.toFinset_mk_eq])
end Oberwolfach
