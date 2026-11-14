module

public import Oberwolfach.OrdinarySampledCoverDegree
public import Oberwolfach.OrdinaryTriangleRootFirstSafeSampleEvent
public import Oberwolfach.OrdinaryTriangleReferenceFreshOrderedRates
public import Oberwolfach.OrdinaryTriangleLikelyCoverCertificate

@[expose] public section
/-! The ordered root-reference and fresh-factor event directly gives the
triangle chain certificate, retaining its exact reference law and sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_safe_ordered_reference_certificate_sampled_cover
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell ζ βe βh loss rate cost deepCost δsample:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (hn:16≤Fintype.card V) (hloss:loss+1/(Fintype.card (V⊕U):ℝ)≤1/4)
    (hcost:rate*Fintype.card (V⊕U)≤cost) (hdeep:rate*Fintype.card (V⊕U)≤deepCost)
    (hprob:1-(loss+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))-1/(Fintype.card (V⊕U):ℝ)≤μ.probability (fun σ=>
      OrdinaryTriangleRootFirstSafeCleanupSample Q F H X T Z W
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
      OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
        ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U)) ∧
      ν+η+4*p≤rate)):
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost :=by
  let E:=fun σ:Sym2 (V⊕U)→Bool=>
    OrdinaryTriangleRootFirstSafeCleanupSample Q F H X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
    OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
    OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ ∧
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
      ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U)) ∧
    ν+η+4*p≤rate
  have hprob':1-((loss+1/(Fintype.card (V⊕U):ℝ))+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))≤μ.probability E:=by
    dsimp [E] at *
    linarith only [hprob]
  refine ⟨μ,E,loss+1/(Fintype.card (V⊕U):ℝ),rate*Fintype.card (V⊕U),rate,hn,hloss,hprob',?_,le_rfl,hcost,hdeep⟩
  intro σ hσ
  apply ordinary_protected_cover_down_cost_mono Q F H X T Z W 3
    ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))
    (rate*Fintype.card (V⊕U)) (rate*Fintype.card (V⊕U))
  · exact mul_le_mul_of_nonneg_right hσ.2.2.2.2 (by positivity)
  · exact mul_le_mul_of_nonneg_right hσ.2.2.2.2 (by positivity)
  · exact hσ.2.2.2.1
end Oberwolfach
