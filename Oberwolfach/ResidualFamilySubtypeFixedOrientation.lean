module

public import Oberwolfach.ResidualSubtypeModel
public import Oberwolfach.ResidualFamilyFixedOrientation

@[expose] public section
/-! Orient the factors first, then restrict every residual source model to
its own surviving-vertex type. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type}
  [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem two_factor_family_fixed_orientation_residual_subtype
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2):
    ∃ (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀ (H:∀i,SimpleGraph (X i)) (R:∀i,Finset (X i)),
        (∀i,H i≤F i)→(∀i x,x∉R i→∀y,¬(H i).Adj x y)→
        ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈R i}),
          (∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
          (∀i p,p∈pieces i→p.Shape ∧ p.OriginalValid (fun x y=>D i x.1 y.1)) ∧
          (∀i,prescribedDependentVertices pieces i=Finset.univ) ∧
          (∀i,prescribedDependentGraph pieces i=(H i).induce (↑(R i):Set (X i))) ∧
          ∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (H i).Adj x.1 y.1 := by
  obtain ⟨D,orig,hpair,hcycles,hwhole,hD,hres⟩:=two_factor_family_fixed_orientation_for_all_subgraphs F hF
  refine ⟨D,orig,hpair,hcycles,hwhole,hD,?_⟩
  intro H R hHF hisol
  obtain ⟨ps,hps,hvalid,hvertices,hgraph,harcs⟩:=hres H R hHF hisol
  choose qs hmap hpair' hvalid' hvertices' hgraph' harcs' using fun i=>
    residual_subtype_model (R i) (H i) (D i) (ps i) (hps i) (hvalid i) (hvertices i) (hgraph i) (harcs i)
  refine ⟨qs,hpair',hvalid',?_,?_,?_⟩
  · intro i;exact hvertices' i
  · intro i;exact hgraph' i
  · intro i x y;exact harcs' i x y
end Oberwolfach
