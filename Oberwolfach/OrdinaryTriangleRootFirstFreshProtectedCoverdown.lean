module

public import Oberwolfach.OrdinaryTriangleRootFirstPrecoverSelection
public import Oberwolfach.OrdinaryTriangleRootFirstSelectedProtected
public import Oberwolfach.OrdinaryRootFirstPrecoverSelectionData
public import Oberwolfach.OrdinaryRootFirstCleanupRemainder
public import Oberwolfach.OrdinaryTriangleSelectedFactors

@[expose] public section
/-! The fresh triangle factors can be selected after the root-first cleanup
    while avoiding the same protected deeper block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_fresh_protected_coverdown
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X T Z W 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W 3 η ell t ν Droot σ)
    (p ρ ζ εsup:ℝ) (ht:0≤t) (hp:0≤p) (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hgood:MixedFreshBoundaryAvoidingEvent p ρ ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      (ordinary_boundary_root_domains_disjoint Q H X Z) σ)
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (hdeg:(p+εsup)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U))
    (hpair:(p^2+εsup)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U))
    (hscaleY:∀j:{u:U // u∉Z},t+ν+ell≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))
    (hscaleZ:∀i:{v:V // v∉X},t+ν+ell≤ζ*(p*(ordinaryBoundaryRowSet H X Z i).card))
    (hbudgetY:∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))
    (hbudgetZ:∀i:{v:V // v∉X},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryRowSet H X Z i).card)):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
      (ν+η+2*(ρ*Fintype.card (V⊕U))) (ν+η+2*(ρ*Fintype.card (V⊕U))) :=by
  obtain ⟨Sel⟩:=ordinary_triangle_root_first_precover_selected_factors Q Qfactor F H Hfactor X T Z W η ell t ν Droot σ O
    p ρ ζ εsup ht hp hbal hdiv hgood hsample hbase hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
  exact ordinary_triangle_root_first_selected_protected Q F H X T Z W η ell t ν Droot σ O hQF hbal hdiv
    (2*(ρ*Fintype.card (V⊕U))) Sel
end Oberwolfach
