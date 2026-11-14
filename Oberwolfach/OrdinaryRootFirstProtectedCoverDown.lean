module

public import Oberwolfach.OrdinaryProtectedHostCoverDownResult
public import Oberwolfach.OrdinaryRootFirstLevelFromFinish
public import Oberwolfach.OrdinaryHostDecomposedRemainder
public import Oberwolfach.OrdinaryBoundaryRemainderLevel

@[expose] public section
/-! A finished root-first construction is a protected cover-down step in
the resource-chain interface, retaining both deep invariants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_protected_coverdown
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ) (limit:ℝ)
    (E:OrdinaryRootFirstFinishData Q F H X T Z W r η ell t ν D σ O limit)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W r (ν+η+limit) (ν+η):=by
  let B:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t O.context
  let SB:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t O.context
  let C:=wheelFamilyRim O.cleanup.wheels
  let SC:=wheelFamilySpokes O.cleanup.wheels
  let R:=(((O.context.cover.rim⊔B)⊔C)⊔E.rim)
  let S:=fun v u=>((O.context.cover.spokes v u∨SB v u)∨SC v u)∨E.spokes v u
  have hl:=ordinary_root_first_level_from_finish Q F H X T Z W r η ell t ν D σ O limit E hbal hdiv
  have hr:=ordinary_host_decomposed_remainder Q R F H S r hl.1 hl.2.1 hbal hdiv
  have hnext:=ordinary_boundary_decomposition_remainder_level Q R H S r X Z (ν+η+limit)
    hr.1 hr.2.1 hl.2.1 hbal hdiv hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2.1
  exact ⟨R,S,hr.1,hr.2.1,hl.1,hnext.2.2.2.2.1,hnext.2.2.1,hnext.2.2.2.1,
    hl.2.2.2.2.1,hl.2.2.2.2.2.1,hl.2.2.2.2.2.2⟩
end Oberwolfach
