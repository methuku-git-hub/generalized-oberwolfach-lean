module

public import Oberwolfach.OrdinaryTriangleSelectedFactorsAutomaticDeepAvoidance
public import Oberwolfach.OrdinaryBoundaryClassesAvoidDeep
public import Oberwolfach.OrdinaryRootFirstCleanupRemainder
public import Oberwolfach.OrdinaryTriangleRootFirstProtectedFromFactors

@[expose] public section
/-! The root-first cleanup clears the deep-to-outside resources. Therefore
    any factors on the actual remaining boundary classes avoid the deeper block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_selected_protected
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X T Z W 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W 3 η ell t ν Droot σ)
    (hQF:Disjoint Q F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card) (limit:ℝ):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W 3 η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W 3 η ell t ν Droot σ O;
    OrdinaryTriangleSelectedFactors Q₂ F H₂ (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
      (ordinaryBoundaryHubSet H Z X) (ordinaryBoundaryHubSet H₂ Z X)
      (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) limit→
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3 (ν+η+limit) (ν+η+limit) :=by
  intro Q₂ H₂ Sel
  obtain ⟨_,_,_,_,_,hRim,hSpokeT,hSpokeW⟩:=ordinary_root_first_cleanup_remainder Q F H X T Z W 3 η ell t ν Droot σ O hbal hdiv
  have hclasses:=ordinary_boundary_classes_avoid_deep Q₂ H₂ X T Z W hRim hSpokeT hSpokeW
  have hDeep:=ordinary_triangle_selected_factors_automatically_avoid_deep Q₂ F H₂
    (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
    (ordinaryBoundaryHubSet H Z X) (ordinaryBoundaryHubSet H₂ Z X)
    (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) limit Sel T W hclasses.1 hclasses.2.1 hclasses.2.2
  exact ordinary_triangle_root_first_protected_from_factors Q F H X T Z W η ell t ν Droot σ O hQF hbal hdiv
    (ordinaryBoundaryHubSet H Z X) limit Sel hDeep.1 hDeep.2
end Oberwolfach
