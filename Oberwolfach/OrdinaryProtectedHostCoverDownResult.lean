module

public import Oberwolfach.OrdinaryGeneralHostCoverDownResult
public import Oberwolfach.OrdinaryDeepBoundaryFourPieces
public import Oberwolfach.OrdinaryDeepBlocker

@[expose] public section
/-! A cover-down step retains its smaller boundary loss and its avoidance
of the protected deeper pair, in addition to the usual level result. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryProtectedHostCoverDownResult (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (cost deepCost:ℝ):Prop:=
  ∃A:SimpleGraph V,∃S:V→U→Prop,
    A≤Q ∧ (∀v u,S v u→H v u) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A S) ∧
    let Qnext:=Q\A;let Hnext:=fun v u=>H v u∧¬S v u;
    ordinaryHostResources Qnext Hnext⊆ordinaryRootResources X Z ∧
    (∀v,Qnext.degree v=2*(Finset.univ.filter (Hnext v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hnext v u)).card) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph A S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph A S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤deepCost) ∧
    Disjoint (ordinaryPhysicalGraph A S) (ordinaryDeepBlocker T W)
end Oberwolfach
