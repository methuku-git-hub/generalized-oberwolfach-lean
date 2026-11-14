module

public import Oberwolfach.FactorDirectedSourceList

@[expose] public section
/-! Every spanning subgraph of a two-factor, with isolated deleted vertices
removed, is represented exactly by disjoint directed path and cycle pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_subgraph_ordered_source_pieces (F H:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (hHF:H≤F) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y):
    ∃ (D:V→V→Prop) (ps:List (PrescribedSourcePiece V)),
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.OriginalValid D) ∧
      sourcePieceVerticesUnion ps=R ∧ sourcePieceEdgesUnion ps=H.edgeFinset ∧
      ∀x y,D x y→F.Adj x y := by
  obtain ⟨D,orig,hpair,hcycles,hverts,hedges,hD⟩:=two_factor_directed_source_cycles F hF
  obtain ⟨ps,hps,hvalid,hvertices,hedges'⟩:=retained_cycle_family_source_pieces H R hisol D orig hpair hcycles
  refine ⟨D,ps,hps,hvalid,?_,?_,hD⟩
  · ext x
    rw [hvertices x,hverts]
    simp
  · rw [hedges',hedges]
    ext e
    simp only [Finset.mem_filter]
    have hsub:H.edgeFinset⊆F.edgeFinset := SimpleGraph.edgeFinset_mono hHF
    constructor
    · exact And.right
    · intro he
      exact ⟨hsub he,he⟩
end Oberwolfach
