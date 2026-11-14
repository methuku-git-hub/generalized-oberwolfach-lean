module

public import Oberwolfach.ResidualSubtypeIndependent

@[expose] public section
/-! Combine fixed factor orientations, exact residual models and the
prescribed-position inputs, with orientations fixed before the residuals. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type}
  [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem two_factor_family_residual_ready_for_positions
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2):
    ∃ (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀ (H:∀i,SimpleGraph (X i)) (R A:∀i,Finset (X i)),
        (∀i,H i≤F i)→(∀i x,x∉R i→∀y,¬(H i).Adj x y)→
        (∀i,A i⊆R i)→(∀i x,x∈A i→∀y,y∈A i→¬(H i).Adj x y)→
        (∀i,(R i).card≤(H i).edgeFinset.card+(A i).card)→
        ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈R i}),
          (∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
          (∀i p,p∈pieces i→p.Shape ∧ p.OriginalValid (fun x y=>D i x.1 y.1)) ∧
          (∀i,prescribedDependentVertices pieces i=Finset.univ) ∧
          (∀i,prescribedDependentGraph pieces i=(H i).induce (↑(R i):Set (X i))) ∧
          (∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (H i).Adj x.1 y.1) ∧
          (∀i x,x∈residualSubtypeSet (R i) (A i)→∀y,y∈residualSubtypeSet (R i) (A i)→
            ¬(prescribedDependentGraph pieces i).Adj x y) ∧
          ∀i,Fintype.card {x // x∈R i}≤(prescribedArcFinset (prescribedDependentDigraph pieces i)).card+
            (residualSubtypeSet (R i) (A i)).card := by
  obtain ⟨D,orig,hpair,hcycles,hwhole,hD,hres⟩:=two_factor_family_fixed_orientation_residual_subtype F hF
  refine ⟨D,orig,hpair,hcycles,hwhole,hD,?_⟩
  intro H R A hHF hisol hAR hA hcount
  obtain ⟨pieces,hps,hvalid,hvertices,hgraph,harcs⟩:=hres H R hHF hisol
  refine ⟨pieces,hps,hvalid,hvertices,hgraph,harcs,?_,?_⟩
  · intro i
    exact residual_subtype_set_independent (R i) (A i) (H i) (hA i) (pieces i) (hgraph i)
  · intro i
    exact residual_subtype_position_budget (R i) (A i) (H i) (hAR i) (hisol i) (pieces i)
      (fun p hp=>(hvalid i p hp).1) (hps i) (hgraph i) (hcount i)
end Oberwolfach
