module

public import Oberwolfach.ResidualFixedOrientation

@[expose] public section
/-! Recover all residual source pieces from the already chosen cycle
orientation, without choosing a new factor orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem fixed_source_orientation_for_all_subgraphs (F:SimpleGraph V)
    (D:V→V→Prop) (orig:List (PrescribedSourcePiece V))
    (hpair:orig.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hcycles:∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D)
    (hvertices:sourcePieceVerticesUnion orig=Finset.univ)
    (hedges:sourcePieceEdgesUnion orig=F.edgeFinset)
    (hD:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion orig):
    ∀(H:SimpleGraph V) (R:Finset V),H≤F→(∀x,x∉R→∀y,¬H.Adj x y)→
      ∃ps:List (PrescribedSourcePiece V),
        ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
        (∀p∈ps,p.Shape ∧ p.OriginalValid D) ∧
        prescribedDependentVertices (fun _ : Unit=>ps) ()=R ∧
        prescribedDependentGraph (fun _ : Unit=>ps) ()=H ∧
        ∀x y,prescribedDependentDigraph (fun _ : Unit=>ps) () x y ↔ D x y ∧ H.Adj x y:=by
  intro H R hHF hisol
  obtain ⟨ps,hps,hvalid,hv,he,ha⟩:=retained_cycle_family_source_pieces_with_arcs H R hisol D orig hpair hcycles
  have hpsV:sourcePieceVerticesUnion ps=R:=by
    ext x
    rw [hv x,hvertices]
    simp
  have hpsE:sourcePieceEdgesUnion ps=H.edgeFinset:=by
    rw [he,hedges]
    ext e
    simp only [Finset.mem_filter]
    have hsub:H.edgeFinset⊆F.edgeFinset:=SimpleGraph.edgeFinset_mono hHF
    exact ⟨And.right,fun hx=>⟨hsub hx,hx⟩⟩
  refine ⟨ps,hps,?_,?_,?_,?_⟩
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
    rw [dependent_source_arcs_of_list,ha,Finset.mem_filter,←hD x y]
end Oberwolfach
