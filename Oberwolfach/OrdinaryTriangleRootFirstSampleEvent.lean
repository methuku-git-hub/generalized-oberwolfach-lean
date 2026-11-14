module

public import Oberwolfach.OrdinaryTriangleRootFirstProtectedScaled
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.OrdinaryBoundaryLocalEvents

@[expose] public section
/-! Intersect the root-first cleanup and fresh-factor events on the same
    physical-edge sample, retaining the protected cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryTriangleFreshFactorSample (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop)
    (X:Finset V) (Z:Finset U) (p ζ εsup:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop :=
  BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ ∧
  MixedFreshBoundaryAvoidingEvent p (2*p) ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
    (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
    (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
    (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val))
    (ordinary_boundary_root_domains_disjoint Q H X Z) σ

def OrdinaryTriangleRootFirstCleanupSample (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 η ell) (p βe βh:ℝ)
    (σ:Sym2 (V⊕U)→Bool):Prop :=
  Nonempty (OrdinaryRootFirstCleanupOutcome Q F H X T Z W 3 η ell t ν D σ) ∧
  OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) X βe p σ ∧
  OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ

structure OrdinaryTriangleRootFirstScaledConditions (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (p εsup τ ν η ell κ ζ:ℝ):Prop where
  hp:0<p
  hp1:p≤1
  hτ:0≤τ
  hκ:0<κ
  hζ:0<ζ
  hε:εsup≤p^2/4
  hsupport:τ+ν≤p^2/4
  hclass:τ+ν+ell≤ζ*κ*p/4
  hblock:ν+η≤ζ*κ*p/4
  hpκ:p≤4*ζ*κ
  hsqrt:20*Real.sqrt (2*p)≤ζ*κ/2
  horder:2≤ζ*κ*p*Fintype.card (V⊕U)/4
  hY:∀j:{u:U // u∉Z},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H Z X j).card:ℝ)
  hZ:∀i:{v:V // v∉X},κ*Fintype.card (V⊕U)≤((ordinaryBoundaryRowSet H X Z i).card:ℝ)

theorem ordinary_triangle_root_first_same_sample_event
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell κ ζ βe βh:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (hnum:OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν η ell κ ζ)
    (hQF:Disjoint Q F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (a b:ℝ)
    (hclean:1-a≤μ.probability (OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh))
    (hfresh:1-b≤μ.probability (OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup)):
    1-a-b≤μ.probability (fun σ=>
      OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
      OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
        ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))) :=by
  let Clean:=OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
    (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
    (ν*Fintype.card (V⊕U)) D p βe βh
  let Fresh:=OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup
  have hi:=finiteLaw_intersection_lower μ Clean Fresh a b hclean hfresh
  apply hi.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  obtain ⟨⟨O⟩,_,_⟩:=hσ.1
  obtain ⟨hsample,hgood⟩:=hσ.2
  refine ⟨hσ.1,hσ.2,?_⟩
  exact ordinary_triangle_root_first_protected_scaled Q Qfactor F H Hfactor X T Z W p εsup τ ν η ell κ ζ
    D σ O hnum.hp hnum.hp1 hnum.hτ hnum.hκ hnum.hζ hnum.hε hnum.hsupport hnum.hclass hnum.hblock
    hnum.hpκ hnum.hsqrt hnum.horder hnum.hY hnum.hZ hQF hbal hdiv hgood hsample hbase
end Oberwolfach
