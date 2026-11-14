module

public import Oberwolfach.OrdinaryTriangleRootFirstSafeSampleEvent
public import Oberwolfach.OrdinaryTriangleRootFreeProtectedScaledSampledCover
public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent

@[expose] public section
/-! The protected cover-down uses the cleanup outcome; the cleanup tests
may be restricted to vertices outside the protected deeper set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryTriangleRootFreeSafeCleanupSample (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 η ell) (p βe βh:ℝ)
    (σ:Sym2 (V⊕U)→Bool):Prop :=
  (∃O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W 3 η ell t ν D σ,
    Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels)
      (wheelFamilySpokes O.cleanup.wheels)) (ordinaryDeepRootStar T W)) ∧
  OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) (X\T) (βe/2) p σ ∧
  OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ

theorem ordinary_triangle_root_free_safe_same_sample_event_sampled_cover
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell κ ζ βe βh δsample:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (hnum:OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν η (p*ell+δsample) κ ζ)
    (hQF:Disjoint Q F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (a b:ℝ)
    (hclean:1-a≤μ.probability (OrdinaryTriangleRootFreeSafeCleanupSample Q F H X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh))
    (hfresh:1-b≤μ.probability (OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup))
    (c:ℝ) (hcover:1-c≤μ.probability (OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample)):
    1-a-b-c≤μ.probability (fun σ=>
      OrdinaryTriangleRootFreeSafeCleanupSample Q F H X T Z W
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
      OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
        ((ν+η+4*p)*Fintype.card (V⊕U)) (η*Fintype.card (V⊕U))) :=by
  let Clean:=OrdinaryTriangleRootFreeSafeCleanupSample Q F H X T Z W
    (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
    (ν*Fintype.card (V⊕U)) D p βe βh
  let Fresh:=OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup
  have hi:=finiteLaw_intersection_lower μ Clean Fresh a b hclean hfresh
  have hi':1-(a+b)≤μ.probability (fun σ=>Clean σ ∧ Fresh σ):=by linarith only [hi]
  have hj:=finiteLaw_intersection_lower μ (fun σ=>Clean σ ∧ Fresh σ)
    (OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample) (a+b) c hi' hcover
  have hj':1-a-b-c≤μ.probability (fun σ=>(Clean σ ∧ Fresh σ) ∧
    OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ):=by linarith only [hj]
  apply hj'.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  obtain ⟨⟨O,hcleanup⟩,_,_⟩:=hσ.1.1
  obtain ⟨hsample,hgood⟩:=hσ.1.2
  refine ⟨hσ.1.1,hσ.1.2,hσ.2,?_⟩
  exact ordinary_triangle_root_free_protected_scaled_sampled_cover Q Qfactor F H Hfactor X T Z W p εsup τ ν η ell κ ζ δsample
    D σ O hcleanup hnum.hp hnum.hp1 hnum.hτ hnum.hκ hnum.hζ hnum.hε hnum.hsupport hnum.hclass hnum.hblock
    hnum.hpκ hnum.hsqrt hnum.horder hnum.hY hnum.hZ hQF hbal hdiv hgood hsample hbase hσ.2
end Oberwolfach
