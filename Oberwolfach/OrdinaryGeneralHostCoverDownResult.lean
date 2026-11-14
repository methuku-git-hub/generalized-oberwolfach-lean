module

public import Oberwolfach.OrdinaryGeneralFinishHostResult

@[expose] public section
/-! A controlled general-length wheel level retaining the actual host and
all-pairs forbidden condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryGeneralHostCoverDownResult (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (r:ℕ) (t:ℝ):Prop:=
  ∃A:SimpleGraph V,∃S:V→U→Prop,
    A≤Q ∧ (∀v u,S v u→H v u) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A S) ∧
    let Qnext:=Q\A;let Hnext:=fun v u=>H v u∧¬S v u;
    ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
    (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤t)
end Oberwolfach
