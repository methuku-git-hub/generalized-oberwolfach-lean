module

public import Oberwolfach.OrdinaryTriangleCanonicalRootFirstFinish
public import Oberwolfach.OrdinaryRootFirstProtectedFromDeepFinish

@[expose] public section
/-! The canonical triangle factors selected on the cleaned sample finish
the root-first construction and give a protected cover-down step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_protected_from_factors
    (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X Tdeep Z Wdeep 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ)
    (hQF:Disjoint Q F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (T:{u:U // u∉Z}→Finset V) (limit:ℝ):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    ∀C:OrdinaryTriangleSelectedFactors Q₂ F H₂ (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
      T (ordinaryBoundaryHubSet H₂ Z X) (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) limit,
    (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (ordinaryDeepBlocker Tdeep Wdeep))→
    (∀i,Disjoint (endpointFactorGraph (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z i) (C.row i))
      (ordinaryDeepBlocker Tdeep Wdeep))→
    OrdinaryProtectedHostCoverDownResult Q F H X Tdeep Z Wdeep 3 (ν+η+limit) (ν+η+limit):=by
  intro Q₂ H₂ C hhub hrow
  obtain ⟨E⟩:=ordinary_triangle_canonical_root_first_finish Q F H X Tdeep Z Wdeep η ell t ν Droot σ O hQF T limit C hhub hrow
  exact ordinary_root_first_protected_from_deep_finish Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O limit E hbal hdiv
end Oberwolfach
