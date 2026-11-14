module

public import Oberwolfach.OrdinaryTriangleReferenceCoverCertificate
public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent

@[expose] public section
/-! The root-first and fresh-factor estimates directly supply the local
triangle certificate used by the corrected-reservoir level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_root_first_likely_certificate
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell κ ζ βe βh rate cost deepCost:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (hnum:OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν η ell κ ζ)
    (hQF:Disjoint Q F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (a b:ℝ) (hn:16≤Fintype.card V) (hloss:a+b≤1/4)
    (hrate:ν+η+4*p≤rate)
    (hcost:rate*Fintype.card (V⊕U)≤cost) (hdeep:rate*Fintype.card (V⊕U)≤deepCost)
    (hclean:1-a≤μ.probability (OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh))
    (hfresh:1-b≤μ.probability (OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup)):
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost :=by
  have hprob:=ordinary_triangle_root_first_same_sample_event Q Qfactor F H Hfactor X T Z W
    p εsup τ ν η ell κ ζ βe βh D hnum hQF hbal hdiv hbase μ a b hclean hfresh
  apply ordinary_triangle_reference_cover_certificate Q Qfactor F H Hfactor X T Z W
    p εsup τ ν η ell ζ βe βh (a+b) rate cost deepCost D μ hn hloss hrate hcost hdeep
  have h2:0≤2/(Fintype.card (V⊕U):ℝ):=by positivity
  have h1:0≤1/(Fintype.card V:ℝ):=by positivity
  have h1':0≤1/(Fintype.card (V⊕U):ℝ):=by positivity
  linarith only [hprob,h2,h1,h1']
end Oberwolfach
