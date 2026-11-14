module

public import Oberwolfach.OrdinaryTriangleFinishAfterCleanup

@[expose] public section
/-! Named conclusion of one triangle boundary finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryTriangleFinishResult (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (p:ℝ):Prop:=
    ∃A:SimpleGraph V,∃S:V→U→Prop,
      A≤Q ∧ (∀v u,S v u→H v u) ∧ HasOrdinaryWheelDecomposition A S 3 ∧
      let Qnext:=Q\A;let Hnext:=fun v u=>H v u∧¬S v u;
      Qnext≤spanningRestriction Q X ∧ (∀v u,Hnext v u→H v u∧v∈X∧u∈Z) ∧
      (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
      ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)
        ≤2*((2*p)*Fintype.card (V⊕U)))
end Oberwolfach
