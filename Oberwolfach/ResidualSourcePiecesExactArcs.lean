module

public import Oberwolfach.ResidualCycleFamilyPiecesWithArcs
public import Oberwolfach.FactorDirectedSourceList

@[expose] public section
/-! The residual pieces preserve exactly the retained arcs of one fixed
orientation of the original two-factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_subgraph_source_pieces_exact_arcs (F H:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (hHF:H≤F) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y):
    ∃ (D:V→V→Prop) (orig ps:List (PrescribedSourcePiece V)),
      orig.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D) ∧
      sourcePieceVerticesUnion orig=Finset.univ ∧ sourcePieceEdgesUnion orig=F.edgeFinset ∧
      (∀x y,D x y ↔ (x,y)∈sourcePieceArcsUnion orig) ∧
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.OriginalValid D) ∧ sourcePieceVerticesUnion ps=R ∧
      sourcePieceEdgesUnion ps=H.edgeFinset ∧
      sourcePieceArcsUnion ps=(sourcePieceArcsUnion orig).filter (fun e=>H.Adj e.1 e.2) := by
  obtain ⟨D₀,orig,hpair,hcycles,hvertices,hedges,hD₀⟩:=two_factor_directed_source_cycles F hF
  let D:V→V→Prop:=fun x y=>(x,y)∈sourcePieceArcsUnion orig
  have hcycles':∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D := by
    intro p hp
    obtain ⟨a,xs,rfl,hvalid⟩:=hcycles p hp
    refine ⟨a,xs,rfl,hvalid.1,hvalid.2.1,?_⟩
    apply (prescribed_directed_edges_chain D ((a::xs)++[a])).2
    intro e he
    exact Finset.mem_biUnion.mpr ⟨.cycle a xs,List.mem_toFinset.mpr hp,he⟩
  obtain ⟨ps,hps,hvalid,hv,he,ha⟩:=retained_cycle_family_source_pieces_with_arcs H R hisol D orig hpair hcycles'
  refine ⟨D,orig,ps,hpair,hcycles',hvertices,hedges,by intro x y;rfl,hps,hvalid,?_,?_,ha⟩
  · ext x
    rw [hv x,hvertices]
    simp
  · rw [he,hedges]
    ext e
    simp only [Finset.mem_filter]
    have hsub:H.edgeFinset⊆F.edgeFinset := SimpleGraph.edgeFinset_mono hHF
    constructor
    · exact And.right
    · intro hx;exact ⟨hsub hx,hx⟩
end Oberwolfach
