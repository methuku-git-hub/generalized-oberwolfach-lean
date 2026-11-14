module

public import Oberwolfach.ResidualFixedOrientation

@[expose] public section
/-! Fix all factor orientations before choosing any of their residual
subgraphs, then construct their exact dependent source models. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type}
  [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem two_factor_family_fixed_orientation_for_all_subgraphs
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2):
    ∃ (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀ (H:∀i,SimpleGraph (X i)) (R:∀i,Finset (X i)),
        (∀i,H i≤F i)→(∀i x,x∉R i→∀y,¬(H i).Adj x y)→
        ∃ pieces:∀i,List (PrescribedSourcePiece (X i)),
          (∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
          (∀i p,p∈pieces i→p.Shape ∧ p.OriginalValid (D i)) ∧
          (∀i,prescribedDependentVertices pieces i=R i) ∧
          (∀i,prescribedDependentGraph pieces i=H i) ∧
          ∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x y ∧ (H i).Adj x y := by
  choose D orig hpair hcycles hvertices hedges hD hsub using
    fun i=>two_factor_fixed_orientation_for_all_subgraphs (F i) (hF i)
  refine ⟨D,orig,hpair,hcycles,?_,hD,?_⟩
  · intro i;exact ⟨hvertices i,hedges i⟩
  · intro H R hHF hisol
    choose pieces hps hvalid hv he ha using
      fun i=>hsub i (H i) (R i) (hHF i) (hisol i)
    refine ⟨pieces,hps,hvalid,?_,?_,?_⟩
    · intro i;exact hv i
    · intro i;exact he i
    · intro i x y;exact ha i x y
end Oberwolfach
