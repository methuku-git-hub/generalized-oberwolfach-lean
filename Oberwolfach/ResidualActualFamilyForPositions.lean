module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualFamilySubtypeReady
public import Oberwolfach.EdgeFinsetInstances

@[expose] public section
/-! The actual selected path and cycle deletions give admissible source pieces
for prescribed-position embedding, using one orientation fixed for each factor
before the deletions are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_factor_residuals_ready_for_positions
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2):
    ∃ (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i))),
      (∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i)) ∧
      (∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset) ∧
      (∀i x y,D i x y ↔ (x,y)∈sourcePieceArcsUnion (orig i)) ∧
      ∀ a:∀i,ActualResidualData (K:=K) (J:=J) (F i),
        ∃ pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}),
          (∀i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
          (∀i p,p∈pieces i→p.Shape ∧ p.OriginalValid (fun x y=>D i x.1 y.1)) ∧
          (∀i,prescribedDependentVertices pieces i=Finset.univ) ∧
          (∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (X i))) ∧
          (∀i x y,prescribedDependentDigraph pieces i x y ↔ D i x.1 y.1 ∧ (a i).graph.Adj x.1 y.1) ∧
          (∀i x,x∈residualSubtypeSet (a i).remaining (a i).prescribed→
            ∀y,y∈residualSubtypeSet (a i).remaining (a i).prescribed→
              ¬(prescribedDependentGraph pieces i).Adj x y) ∧
          (∀i,Fintype.card {x // x∈(a i).remaining}≤
            (prescribedArcFinset (prescribedDependentDigraph pieces i)).card+
              (residualSubtypeSet (a i).remaining (a i).prescribed).card) ∧
          (∀i,(a i).oldDomain∩(a i).remaining=(a i).prescribed) ∧
          (∀ (i:I) (x:{x // x∈(a i).remaining}),
            x∈residualSubtypeSet (a i).remaining (a i).prescribed ↔ x.1∈(a i).oldDomain) := by
  obtain ⟨D,orig,hpair,hcycles,hwhole,hD,hres⟩:=two_factor_family_residual_ready_for_positions F hF
  refine ⟨D,orig,hpair,hcycles,hwhole,hD,?_⟩
  intro a
  have hf:∀i,(a i).graph≤F i ∧ (a i).prescribed⊆(a i).remaining ∧
      (∀x∈(a i).prescribed,∀y∈(a i).prescribed,¬(a i).graph.Adj x y) ∧
      (a i).remaining.card≤(a i).graph.edgeFinset.card+(a i).prescribed.card ∧
      (∀x,x∉(a i).remaining→∀y,¬(a i).graph.Adj x y) ∧
      (a i).oldDomain∩(a i).remaining=(a i).prescribed :=
    fun i=>(a i).graph_facts (hF i)
  obtain ⟨pieces,hp,hv,hu,hg,ha,hi,hcount⟩:=hres
    (fun i=>(a i).graph) (fun i=>(a i).remaining) (fun i=>(a i).prescribed)
    (fun i=>(hf i).1) (fun i=>(hf i).2.2.2.2.1) (fun i=>(hf i).2.1)
    (fun i=>(hf i).2.2.1) (by
      intro i
      convert (hf i).2.2.2.1 using 1 <;> congr 1 <;> apply edge_finset_card_independent)
  refine ⟨pieces,hp,hv,hu,hg,ha,hi,hcount,fun i=>(hf i).2.2.2.2.2,?_⟩
  intro i x
  simp only [residualSubtypeSet,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [←(hf i).2.2.2.2.2,Finset.mem_inter]
  exact ⟨And.left,fun hx=>⟨hx,x.2⟩⟩
end Oberwolfach
