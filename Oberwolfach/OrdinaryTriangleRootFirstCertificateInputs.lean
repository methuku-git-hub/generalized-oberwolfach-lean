module

public import Oberwolfach.OrdinaryTriangleRootFirstLikelyCertificate

@[expose] public section
/-! Explicit local inputs for a triangle certificate, including both
probability estimates on the same physical-edge sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryTriangleRootFirstCertificateInputs
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (cost deepCost:ℝ) where
  Qfactor:SimpleGraph V
  Hfactor:V→U→Prop
  p:ℝ
  εsup:ℝ
  τ:ℝ
  ν:ℝ
  η:ℝ
  ell:ℝ
  κ:ℝ
  ζ:ℝ
  βe:ℝ
  βh:ℝ
  rate:ℝ
  D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))
  hnum:OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν η ell κ ζ
  hQF:Disjoint Q F
  hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card
  hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card
  hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)
  μ:FiniteLaw (Sym2 (V⊕U)→Bool)
  a:ℝ
  b:ℝ
  hn:16≤Fintype.card V
  hloss:a+b≤1/4
  hrate:ν+η+4*p≤rate
  hcost:rate*Fintype.card (V⊕U)≤cost
  hdeep:rate*Fintype.card (V⊕U)≤deepCost
  hclean:1-a≤μ.probability (OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
    (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
    (ν*Fintype.card (V⊕U)) D p βe βh)
  hfresh:1-b≤μ.probability (OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup)

theorem ordinary_triangle_root_first_certificate_of_inputs
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (cost deepCost:ℝ)
    (inputs:OrdinaryTriangleRootFirstCertificateInputs Q F H X T Z W cost deepCost):
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost :=by
  exact ordinary_triangle_root_first_likely_certificate Q inputs.Qfactor F H inputs.Hfactor X T Z W
    inputs.p inputs.εsup inputs.τ inputs.ν inputs.η inputs.ell inputs.κ inputs.ζ inputs.βe inputs.βh
    inputs.rate cost deepCost inputs.D inputs.hnum inputs.hQF inputs.hbal inputs.hdiv inputs.hbase
    inputs.μ inputs.a inputs.b inputs.hn inputs.hloss inputs.hrate inputs.hcost inputs.hdeep inputs.hclean inputs.hfresh
end Oberwolfach
