module

public import Oberwolfach.OrdinaryProtectedHostCoverDownResult
public import Oberwolfach.OrdinaryBoundaryRemainderLevel

@[expose] public section
/-! Package an actual protected wheel level in the level-chain interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_level_protected_coverdown
    (Q R F:SimpleGraph V) (H S:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (cost deepCost:ℝ)
    (hR:R≤Q) (hS:∀v u,S v u→H v u)
    (hhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S))
    (hdec:HasOrdinaryWheelDecomposition R S r)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hRin:(Q\R).support⊆(X:Set V)) (hSin:∀v u,H v u∧¬S v u→v∈X∧u∈Z)
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost)
    (hdeepcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤deepCost)
    (hdeep:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W)):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W r cost deepCost:=by
  have hnext:=ordinary_boundary_decomposition_remainder_level Q R H S r X Z cost hR hS hdec hbal hdiv hRin hSin hcost
  exact ⟨R,S,hR,hS,hhost,hnext.2.2.2.2.1,hnext.2.2.1,hnext.2.2.2.1,hcost,hdeepcost,hdeep⟩
end Oberwolfach
