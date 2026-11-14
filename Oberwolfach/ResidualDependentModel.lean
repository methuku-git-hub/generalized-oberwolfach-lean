module

public import Oberwolfach.ResidualTwoFactorSourcePieces
public import Oberwolfach.PrescribedDependentPhysical

@[expose] public section
/-! Identify the constructed pieces with the source model used by the
dependent-family embedding theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem dependent_source_vertices_of_list (ps:List (PrescribedSourcePiece V)):
    prescribedDependentVertices (fun _ : Unit=>ps) ()=sourcePieceVerticesUnion ps := by
  ext x
  simp [prescribedDependentVertices,sourcePieceVerticesUnion]

theorem dependent_source_graph_of_list (ps:List (PrescribedSourcePiece V)) (H:SimpleGraph V)
    (hE:sourcePieceEdgesUnion ps=H.edgeFinset):
    prescribedDependentGraph (fun _ : Unit=>ps) ()=H := by
  ext x y
  rw [prescribedDependentGraph,SimpleGraph.fromEdgeSet_adj]
  have he:s(x,y)∈prescribedDependentPhysical (fun _ : Unit=>ps) () ↔ s(x,y)∈H.edgeFinset := by
    rw [←hE]
    simp [prescribedDependentPhysical,sourcePieceEdgesUnion]
  rw [he,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  exact ⟨fun h=>h.1,fun h=>⟨h,h.ne⟩⟩

theorem two_factor_subgraph_dependent_model (F H:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (hHF:H≤F) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y):
    ∃ (D:V→V→Prop) (ps:List (PrescribedSourcePiece V)),
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.Shape ∧ p.OriginalValid D) ∧
      prescribedDependentVertices (fun _ : Unit=>ps) ()=R ∧
      prescribedDependentGraph (fun _ : Unit=>ps) ()=H ∧
      ∀x y,D x y→F.Adj x y := by
  obtain ⟨D,ps,hpair,hvalid,hverts,hedges,hD⟩:=two_factor_subgraph_ordered_source_pieces F H hF hHF R hisol
  refine ⟨D,ps,hpair,?_,?_,?_,hD⟩
  · intro p hp
    have hh:=hvalid p hp
    constructor
    · cases p with
      | path xs => exact hh.1
      | cycle a xs => exact ⟨hh.1,hh.2.1⟩
    · exact hh
  · rw [dependent_source_vertices_of_list,hverts]
  · exact dependent_source_graph_of_list ps H hedges
end Oberwolfach
