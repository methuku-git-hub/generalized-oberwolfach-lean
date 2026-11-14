module

public import Oberwolfach.OrdinaryHostDecomposedRemainder
public import Oberwolfach.OrdinaryRootFirstLevelFromRootFreeCleanup
public import Oberwolfach.OrdinaryProtectedHostCoverDownResult
public import Oberwolfach.OrdinaryBoundaryRemainderLevel

@[expose] public section
/-! Join the root cover, packing, cleanup and an actual deep-block-avoiding
boundary finish into a balanced protected level step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_protected_from_root_free_cleanup
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ)
    (E:OrdinaryRootFirstFinishData Q F H X T Z W r η ell t ν D σ O limit)
    (hcleanup:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels)
      (wheelFamilySpokes O.cleanup.wheels)) (ordinaryDeepRootStar T W))
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W r (ν+η+limit) η :=by
  let K:=O.context
  let B:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K
  let SB:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K
  let C:=wheelFamilyRim O.cleanup.wheels
  let SC:=wheelFamilySpokes O.cleanup.wheels
  let R:=(((K.cover.rim⊔B)⊔C)⊔E.rim)
  let S:=fun v u=>((K.cover.spokes v u∨SB v u)∨SC v u)∨E.spokes v u
  have hl:=ordinary_root_first_level_from_root_free_cleanup Q F H X T Z W r η ell t ν D σ O limit E hcleanup hbal hdiv
  change HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
    HasOrdinaryWheelDecomposition R S r ∧ (Q\R).support⊆(X:Set V) ∧
    (∀v u,H v u∧¬S v u→v∈X∧u∈Z) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η+limit) ∧
    (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η) ∧
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W) at hl
  have hr:=ordinary_host_decomposed_remainder Q R F H S r hl.1 hl.2.1 hbal hdiv
  have hrem:=ordinary_boundary_decomposition_remainder_level Q R H S r X Z (ν+η+limit)
    hr.1 hr.2.1 hl.2.1 hbal hdiv hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1
  exact ⟨R,S,hr.1,hr.2.1,hl.1,hrem.2.2.2.2.1,hr.2.2.1,hr.2.2.2,
    hl.2.2.2.2.1,hl.2.2.2.2.2.1,hl.2.2.2.2.2.2⟩
end Oberwolfach
