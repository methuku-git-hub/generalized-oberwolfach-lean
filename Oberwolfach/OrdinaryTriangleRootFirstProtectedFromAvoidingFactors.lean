module

public import Oberwolfach.OrdinaryTriangleRootFirstProtectedFromFactors

@[expose] public section
/-! Preserve the same cleanup outcome and selected factors when the factor
selection avoids a graph containing the protected deeper block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_protected_from_avoiding_factors
    (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X Tdeep Z Wdeep 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ)
    (hQF:Disjoint Q F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (T:{u:U // u∉Z}→Finset V) (limit:ℝ) (K:SimpleGraph (V⊕U))
    (hK:ordinaryDeepBlocker Tdeep Wdeep≤K):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    (∃C:OrdinaryTriangleSelectedFactors Q₂ F H₂ (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
      T (ordinaryBoundaryHubSet H₂ Z X) (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z) limit,
      (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U)) K) ∧
      (∀i,Disjoint (endpointFactorGraph (ordinary_boundary_root_domains_disjoint Q₂ H₂ X Z i) (C.row i)) K))→
    OrdinaryProtectedHostCoverDownResult Q F H X Tdeep Z Wdeep 3 (ν+η+limit) (ν+η+limit):=by
  intro Q₂ H₂ hselection
  obtain ⟨C,hhub,hrow⟩:=hselection
  apply ordinary_triangle_root_first_protected_from_factors Q F H X Tdeep Z Wdeep η ell t ν Droot σ O hQF hbal hdiv T limit C
  · intro j;exact (hhub j).mono_right hK
  · intro i;exact (hrow i).mono_right hK
end Oberwolfach
