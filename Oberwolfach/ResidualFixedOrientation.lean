module

public import Oberwolfach.ResidualDependentModelExactArcs

@[expose] public section
/-! Fix the full source orientation before any residual graph or surviving
vertex set is chosen; all later subgraphs retain exactly that orientation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_fixed_orientation_for_all_subgraphs (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2):
    ∃ (D:V→V→Prop) (orig:List (PrescribedSourcePiece V)),
      orig.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D) ∧
      sourcePieceVerticesUnion orig=Finset.univ ∧ sourcePieceEdgesUnion orig=F.edgeFinset ∧
      (∀x y,D x y ↔ (x,y)∈sourcePieceArcsUnion orig) ∧
      ∀ (H:SimpleGraph V) (R:Finset V),H≤F→(∀x,x∉R→∀y,¬H.Adj x y)→
        ∃ ps:List (PrescribedSourcePiece V),
          ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
          (∀p∈ps,p.Shape ∧ p.OriginalValid D) ∧
          prescribedDependentVertices (fun _ : Unit=>ps) ()=R ∧
          prescribedDependentGraph (fun _ : Unit=>ps) ()=H ∧
          ∀x y,prescribedDependentDigraph (fun _ : Unit=>ps) () x y ↔ D x y ∧ H.Adj x y := by
  obtain ⟨D₀,orig,hpair,hcycles,hvertices,hedges,hD₀⟩:=two_factor_directed_source_cycles F hF
  let D:V→V→Prop:=fun x y=>(x,y)∈sourcePieceArcsUnion orig
  have hcycles':∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D := by
    intro p hp
    obtain ⟨a,xs,rfl,hvalid⟩:=hcycles p hp
    refine ⟨a,xs,rfl,hvalid.1,hvalid.2.1,?_⟩
    apply (prescribed_directed_edges_chain D ((a::xs)++[a])).2
    intro e he
    exact Finset.mem_biUnion.mpr ⟨.cycle a xs,List.mem_toFinset.mpr hp,he⟩
  refine ⟨D,orig,hpair,hcycles',hvertices,hedges,by intro x y;rfl,?_⟩
  intro H R hHF hisol
  obtain ⟨ps,hps,hvalid,hv,he,ha⟩:=retained_cycle_family_source_pieces_with_arcs H R hisol D orig hpair hcycles'
  have hpsV:sourcePieceVerticesUnion ps=R := by
    ext x
    rw [hv x,hvertices]
    simp
  have hpsE:sourcePieceEdgesUnion ps=H.edgeFinset := by
    rw [he,hedges]
    ext e
    simp only [Finset.mem_filter]
    have hsub:H.edgeFinset⊆F.edgeFinset := SimpleGraph.edgeFinset_mono hHF
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
    rw [dependent_source_arcs_of_list,ha,Finset.mem_filter]
end Oberwolfach
