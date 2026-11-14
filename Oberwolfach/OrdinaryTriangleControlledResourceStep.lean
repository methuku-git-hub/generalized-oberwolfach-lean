module

public import Oberwolfach.OrdinaryTriangleControlledCoverDown
public import Oberwolfach.OrdinaryTriangleDecompositionHost

@[expose] public section
/-! The controlled triangle cover-down gives a conflict-respecting resource
level step while retaining its actual inner deletion-degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_controlled_resource_step
    (P Q F:SimpleGraph V) (Hbase H:V→U→Prop) (X:Finset V) (Z:Finset U) (t:ℝ)
    (hQP:Q≤P) (hQF:Disjoint Q F) (hH:∀v u,H v u→Hbase v u)
    (hstep:OrdinaryTriangleControlledCoverDownResult Q H X Z t):
    ∃A:SimpleGraph V,∃S:V→U→Prop,
      A≤Q ∧ (∀v u,S v u→H v u) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=3))
        (ordinaryHostResources A S) ∧
      let Qnext:=Q\A;let Hnext:=fun v u=>H v u∧¬S v u;
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤t):=by
  obtain ⟨A,S,hAQ,hSH,hA,hinner,hspoke,hbal,hdiv,hbound⟩:=hstep
  have hdec:=ordinary_triangle_decomposition_in_ambient_host P A F Hbase S
    (hAQ.trans hQP) (hQF.mono_left hAQ) (fun v u h=>hH v u (hSH v u h)) hA
  refine ⟨A,S,hAQ,hSH,hdec,?_,hbal,hdiv,hbound⟩
  intro e he
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      have he':(Q\A).Adj v w:=(ordinaryHostResources_rim (Q\A) _ s(v,w)).mp he
      have hvw:=(spanningRestriction_adj Q X v w).mp (hinner he')
      exact ordinaryRootResources_rim X Z v w hvw.2.1 hvw.2.2
  | inr vu=>
    rcases vu with ⟨v,u⟩
    have he':H v u∧¬S v u:=(ordinaryHostResources_spoke (Q\A) _ v u).mp he
    exact ordinaryRootResources_spoke X Z v u (hspoke v u he').1 (hspoke v u he').2
end Oberwolfach
