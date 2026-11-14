module

public import Oberwolfach.OrdinaryTriangleFreshRootFreeProtectedCoverdown
public import Oberwolfach.OrdinaryRootFirstSelectionMargins

@[expose] public section
/-! The protected triangle cover-down with all deletion costs expressed as
    rates on the same ambient vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_root_free_protected_scaled
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell κ ζ:ℝ)
    (Droot:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W 3 (η*Fintype.card (V⊕U))
      (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) Droot σ)
    (hcleanup:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels)
      (wheelFamilySpokes O.cleanup.wheels)) (ordinaryDeepRootStar T W))
    (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hκ:0<κ) (hζ:0<ζ)
    (hε:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+ell≤ζ*κ*p/4) (hblock:ν+η≤ζ*κ*p/4)
    (hpκ:p≤4*ζ*κ) (hsqrt:20*Real.sqrt (2*p)≤ζ*κ/2)
    (horder:2≤ζ*κ*p*Fintype.card (V⊕U)/4)
    (hY:∀j:{u:U // u∉Z},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H Z X j).card:ℝ))
    (hZ:∀i:{v:V // v∉X},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryRowSet H X Z i).card:ℝ))
    (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hgood:MixedFreshBoundaryAvoidingEvent p (2*p) ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
      (ordinary_boundary_root_domains_disjoint Q H X Z) σ)
    (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
      ((ν+η+4*p)*Fintype.card (V⊕U)) (η*Fintype.card (V⊕U)) :=by
  let n:ℝ:=Fintype.card (V⊕U)
  have hn:0≤n:=by dsimp [n];positivity
  obtain ⟨hdeg,hpair,hmargin⟩:=ordinary_root_first_selection_margins p εsup τ ν η ell κ ζ n
    hp hp1 hκ hζ hn hε hsupport hclass hblock hpκ hsqrt horder
  have ht:0≤τ*n:=mul_nonneg hτ hn
  have hresult:=ordinary_triangle_root_first_fresh_root_free_protected_coverdown Q Qfactor F H Hfactor X T Z W
    (η*n) (ell*n) (τ*n) (ν*n) Droot σ O hcleanup p (2*p) ζ εsup ht hp.le hQF hbal hdiv hgood hsample hbase
    hdeg hpair (fun j=>(hmargin _ (hY j)).1) (fun i=>(hmargin _ (hZ i)).1)
    (fun j=>(hmargin _ (hY j)).2) (fun i=>(hmargin _ (hZ i)).2)
  convert hresult using 1 <;> ring
end Oberwolfach
