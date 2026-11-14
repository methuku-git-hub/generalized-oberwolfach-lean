module

public import Oberwolfach.ResidualDependentModelExactArcs

@[expose] public section
/-! Apply the exact source-model and orientation construction simultaneously
to a family of separately typed two-factor subgraphs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type}
  [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem two_factor_family_dependent_models_exact_arcs
    (F H:∀i,SimpleGraph (X i)) (R:∀i,Finset (X i))
    (hF:∀i,(F i).IsRegularOfDegree 2) (hHF:∀i,H i≤F i)
    (hisol:∀i x,x∉R i→∀y,¬(H i).Adj x y):
    ∃ (D:∀i,X i→X i→Prop) (orig pieces:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈pieces i→p.Shape ∧ p.OriginalValid (D i)) ∧
      (∀i,prescribedDependentVertices pieces i=R i) ∧
      (∀i,prescribedDependentGraph pieces i=H i) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x y ∧ (H i).Adj x y := by
  choose D orig pieces hpair hcycles hvertices hedges hps hvalid hpsV hpsE hD hpsA using
    fun i=>two_factor_subgraph_dependent_model_exact_arcs (F i) (H i) (hF i) (hHF i) (R i) (hisol i)
  refine ⟨D,orig,pieces,hpair,hcycles,?_,hps,hvalid,?_,?_,hD,?_⟩
  · intro i;exact ⟨hvertices i,hedges i⟩
  · intro i;exact hpsV i
  · intro i;exact hpsE i
  · intro i x y;exact hpsA i x y
end Oberwolfach
