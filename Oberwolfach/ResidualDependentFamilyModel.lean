module

public import Oberwolfach.ResidualDependentModel

@[expose] public section
/-! Construct the embedding theorem's source pieces for an arbitrary
family of separately typed two-factor subgraphs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type}
  [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem two_factor_family_subgraph_dependent_models
    (F H:∀i,SimpleGraph (X i)) (R:∀i,Finset (X i))
    (hF:∀i,(F i).IsRegularOfDegree 2) (hHF:∀i,H i≤F i)
    (hisol:∀i x,x∉R i→∀y,¬(H i).Adj x y):
    ∃ (D:∀i,X i→X i→Prop) (pieces:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈pieces i→p.Shape ∧ p.OriginalValid (D i)) ∧
      (∀i,prescribedDependentVertices pieces i=R i) ∧
      (∀i,prescribedDependentGraph pieces i=H i) ∧
      (∀i x y,D i x y→(F i).Adj x y) := by
  choose D pieces hpair hvalid hvertices hgraph hD using
    fun i=>two_factor_subgraph_dependent_model (F i) (H i) (hF i) (hHF i) (R i) (hisol i)
  refine ⟨D,pieces,hpair,hvalid,?_,?_,hD⟩
  · intro i
    exact hvertices i
  · intro i
    exact hgraph i
end Oberwolfach
