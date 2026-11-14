module

public import Oberwolfach.ResidualSourcePiecesExactArcs
public import Oberwolfach.ResidualDependentModel

@[expose] public section
/-! The embedding model preserves the complete original directed arc set
restricted to the residual graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem dependent_source_arcs_of_list (ps:List (PrescribedSourcePiece V)) (x y:V):
    prescribedDependentDigraph (fun _ : Unit=>ps) () x y ↔ (x,y)∈sourcePieceArcsUnion ps := by
  simp [prescribedDependentDigraph,sourcePieceArcsUnion]

theorem two_factor_subgraph_dependent_model_exact_arcs (F H:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (hHF:H≤F) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y):
    ∃ (D:V→V→Prop) (orig ps:List (PrescribedSourcePiece V)),
      orig.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D) ∧
      sourcePieceVerticesUnion orig=Finset.univ ∧ sourcePieceEdgesUnion orig=F.edgeFinset ∧
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.Shape ∧ p.OriginalValid D) ∧
      prescribedDependentVertices (fun _ : Unit=>ps) ()=R ∧
      prescribedDependentGraph (fun _ : Unit=>ps) ()=H ∧
      (∀x y,D x y ↔ (x,y)∈sourcePieceArcsUnion orig) ∧
      ∀x y,prescribedDependentDigraph (fun _ : Unit=>ps) () x y ↔ D x y ∧ H.Adj x y := by
  obtain ⟨D,orig,ps,hpair,hcycles,hverts,hedges,hD,hps,hvalid,hpsV,hpsE,hpsA⟩:=
    two_factor_subgraph_source_pieces_exact_arcs F H hF hHF R hisol
  refine ⟨D,orig,ps,hpair,hcycles,hverts,hedges,hps,?_,?_,?_,hD,?_⟩
  · intro p hp
    have hh:=hvalid p hp
    constructor
    · cases p with
      | path xs => exact hh.1
      | cycle a xs => exact ⟨hh.1,hh.2.1⟩
    · exact hh
  · rw [dependent_source_vertices_of_list,hpsV]
  · exact dependent_source_graph_of_list ps H hpsE
  · intro x y
    rw [dependent_source_arcs_of_list,hpsA,Finset.mem_filter,←hD x y]
end Oberwolfach
