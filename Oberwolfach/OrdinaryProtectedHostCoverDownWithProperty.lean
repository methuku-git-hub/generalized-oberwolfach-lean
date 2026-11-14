module

public import Oberwolfach.OrdinaryProtectedHostCoverDownResult

@[expose] public section
/-! A protected cover-down records a property of the very same wheel deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryProtectedHostCoverDownWithProperty (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (cost deepCost:ℝ) (GoodDel:SimpleGraph V→(V→U→Prop)→Prop):Prop:=
  ∃A:SimpleGraph V,∃S:V→U→Prop,
    A≤Q ∧ (∀v u,S v u→H v u) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A S) ∧
    let Qnext:=Q\A;let Hnext:=fun v u=>H v u∧¬S v u;
    ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
    (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph A S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤deepCost) ∧
    Disjoint (ordinaryPhysicalGraph A S) (ordinaryDeepBlocker T W) ∧ GoodDel A S
end Oberwolfach
