module

public import Oberwolfach.ResidualSubtypeMapMembership
public import Oberwolfach.ResidualFixedOrientation

@[expose] public section
/-! Exact restriction of a fixed-orientation residual model to surviving vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem residual_subtype_model (R:Finset V) (H:SimpleGraph V) (D:V→V→Prop)
    (ps:List (PrescribedSourcePiece V))
    (hp:ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hv:∀p∈ps,p.Shape ∧ p.OriginalValid D)
    (hR:prescribedDependentVertices (fun _ : Unit=>ps) ()=R)
    (hH:prescribedDependentGraph (fun _ : Unit=>ps) ()=H)
    (hD:∀x y,prescribedDependentDigraph (fun _ : Unit=>ps) () x y ↔ D x y ∧ H.Adj x y):
    ∃ qs:List (PrescribedSourcePiece {x // x∈R}),
      qs.map (fun q=>q.map Subtype.val)=ps ∧
      qs.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀q∈qs,q.Shape ∧ q.OriginalValid (fun x y=>D x.1 y.1)) ∧
      prescribedDependentVertices (fun _ : Unit=>qs) ()=Finset.univ ∧
      prescribedDependentGraph (fun _ : Unit=>qs) ()=H.induce (↑R:Set V) ∧
      ∀x y,prescribedDependentDigraph (fun _ : Unit=>qs) () x y ↔ D x.1 y.1 ∧ H.Adj x.1 y.1 := by
  have hR':sourcePieceVerticesUnion ps=R:=by rwa [←dependent_source_vertices_of_list]
  obtain ⟨qs,hmap,hpair,hvalid,hvertices⟩:=source_pieces_on_surviving_subtype R D ps hp hv hR'
  refine ⟨qs,hmap,hpair,hvalid,?_,?_,?_⟩
  · rw [dependent_source_vertices_of_list,hvertices]
  · ext x y
    have hmem:=source_subtype_edges_membership R qs ps hmap s(x,y)
    have hpq:(s(x,y)∈sourcePieceEdgesUnion qs) ↔ s(x.1,y.1)∈sourcePieceEdgesUnion ps:=by simpa using hmem
    have hadj: (prescribedDependentGraph (fun _ : Unit=>ps) ()).Adj x.1 y.1 ↔ H.Adj x.1 y.1 := by rw [hH]
    simp only [prescribedDependentGraph,SimpleGraph.fromEdgeSet_adj] at hadj ⊢
    simp only [sourcePieceEdgesUnion,Finset.mem_biUnion,
      List.mem_toFinset] at hpq
    simp only [prescribedDependentPhysical,Set.mem_ofPred_eq] at hadj ⊢
    have hne:x≠y ↔ x.1≠y.1:=by
      constructor
      · intro h hxy;exact h (Subtype.ext hxy)
      · intro h hxy;exact h (congrArg Subtype.val hxy)
    rw [hne]
    simpa only [SimpleGraph.induce_adj] using (and_congr hpq Iff.rfl).trans hadj
  · intro x y
    rw [dependent_source_arcs_of_list,source_subtype_arcs_membership R qs ps hmap,
      ←dependent_source_arcs_of_list,hD]
end Oberwolfach
