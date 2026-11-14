module

public import Oberwolfach.OrdinaryInnerUnionDegree
public import Oberwolfach.OrdinaryTriangleFinishResult

@[expose] public section
/-! Assemble a whole one-level triangle cover-down from successive
approximate, cleanup and boundary wheel decompositions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryTriangleControlledCoverDownResult (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (t:ℝ):Prop:=
  ∃A:SimpleGraph V,∃S:V→U→Prop,
    A≤Q ∧ (∀v u,S v u→H v u) ∧ HasOrdinaryWheelDecomposition A S 3 ∧
    let Qnext:=Q\A;let Hnext:=fun v u=>H v u∧¬S v u;
    Qnext≤spanningRestriction Q X ∧ (∀v u,Hnext v u→v∈X∧u∈Z) ∧
    (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
    (∀u,3∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤t)

theorem ordinary_triangle_controlled_cover_down_from_three
    (Q A B:SimpleGraph V) (H S T:V→U→Prop) (X:Finset V) (Z:Finset U) (p ν:ℝ)
    (hA:HasOrdinaryWheelDecomposition A S 3) (hB:HasOrdinaryWheelDecomposition B T 3)
    (hAsub:A≤Q) (hSsub:∀v u,S v u→H v u)
    (hBsub:B≤Q\A) (hTsub:∀v u,T v u→H v u∧¬S v u)
    (havoid:Disjoint (ordinaryPhysicalGraph A S) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hBdegree:∀w:V⊕U,((ordinaryPhysicalGraph B T).degree w:ℝ)≤ν*Fintype.card (V⊕U))
    (hfinish:OrdinaryTriangleFinishResult ((Q\A)\B) (fun v u=>(H v u∧¬S v u)∧¬T v u) X Z p):
    OrdinaryTriangleControlledCoverDownResult Q H X Z ((ν+4*p)*Fintype.card (V⊕U)):=by
  obtain ⟨C,W,hCsub,hWsub,hC,hinner,hspoke,hbal,hdiv,_,hfactorinner⟩:=hfinish
  have hseq:=ordinary_three_sequential_decompositions_in_host Q A B C H S T W 3
    hA hB hC hAsub hSsub hBsub hTsub hCsub hWsub
  let J:V→U→Prop:=fun v u=>(S v u∨T v u)∨W v u
  have hJ:(fun v u=>H v u∧¬J v u)=
      (fun v u=>((H v u∧¬S v u)∧¬T v u)∧¬W v u):=by
    funext v u
    exact propext (hseq.2.2.2.2 v u)
  have hQsub:((Q\A)\B)≤Q:=sdiff_le.trans sdiff_le
  have hrestrict:spanningRestriction ((Q\A)\B) X≤spanningRestriction Q X:=by
    intro v w hvw
    rw [spanningRestriction_adj] at hvw ⊢
    exact ⟨hQsub hvw.1,hvw.2⟩
  refine ⟨(A⊔B)⊔C,J,hseq.1,hseq.2.1,hseq.2.2.1,?_,?_,?_,?_,?_⟩
  · rw [hseq.2.2.2.1]
    exact hinner.trans hrestrict
  · intro v u hvu
    have hh:=hspoke v u ((congrFun (congrFun hJ v) u).mp hvu)
    exact hh.2
  · intro v
    have hdeg:(Q\((A⊔B)⊔C)).degree v=(((Q\A)\B)\C).degree v:=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext w
      simp only [SimpleGraph.mem_neighborFinset]
      exact iff_of_eq (congrArg (fun G:SimpleGraph V=>G.Adj v w) hseq.2.2.2.1)
    have hrow:(Finset.univ.filter (fun u=>H v u∧¬J v u))=
        Finset.univ.filter (fun u=>((H v u∧¬S v u)∧¬T v u)∧¬W v u):=by
      ext u
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hseq.2.2.2.2 v u
    have hr:=congrArg Finset.card hrow
    have hh:(((Q\A)\B)\C).degree v=2*(Finset.univ.filter (fun u=>((H v u∧¬S v u)∧¬T v u)∧¬W v u)).card:=by
      convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    convert hdeg.trans (hh.trans (congrArg (fun x:ℕ=>2*x) hr.symm)) using 1 <;>
      congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    have hcol:(Finset.univ.filter (fun v=>H v u∧¬J v u))=
        Finset.univ.filter (fun v=>((H v u∧¬S v u)∧¬T v u)∧¬W v u):=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hseq.2.2.2.2 v u
    have hh:3∣(Finset.univ.filter (fun v=>((H v u∧¬S v u)∧¬T v u)∧¬W v u)).card:=by
      convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hc:=congrArg Finset.card hcol
    have hout:3∣(Finset.univ.filter (fun v=>H v u∧¬J v u)).card:=hc.symm ▸ hh
    convert hout using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · have hh:=ordinary_inner_union_degree Q A B C H S T W X Z
      (ν*Fintype.card (V⊕U)) (2*((2*p)*Fintype.card (V⊕U))) hAsub hSsub havoid hBdegree hfactorinner
    intro w
    convert hh w using 1 <;> ring
end Oberwolfach
