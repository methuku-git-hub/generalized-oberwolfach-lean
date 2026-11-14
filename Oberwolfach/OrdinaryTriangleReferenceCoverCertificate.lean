module

public import Oberwolfach.OrdinaryTriangleLikelyCoverCertificate
public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent

@[expose] public section
/-! The actual reference-and-fresh event provides the per-host certificate
    required by the protected triangle level chain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_reference_cover_certificate
    (Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (p εsup τ ν η ell ζ βe βh loss rate cost deepCost:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)))
    (μ:FiniteLaw (Sym2 (V⊕U)→Bool)) (hn:16≤Fintype.card V) (hloss:loss≤1/4)
    (hrate:ν+η+4*p≤rate)
    (hcost:rate*Fintype.card (V⊕U)≤cost) (hdeep:rate*Fintype.card (V⊕U)≤deepCost)
    (hprob:1-(loss+2/(Fintype.card (V⊕U):ℝ))-
      (1/(Fintype.card V:ℝ)+1/(Fintype.card (V⊕U):ℝ))≤μ.probability (fun σ=>
      OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
      OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
        ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U)))):
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost :=by
  let E:=fun σ:Sym2 (V⊕U)→Bool=>
    OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
    OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
    OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
      ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))
  refine ⟨μ,E,loss,(ν+η+4*p)*Fintype.card (V⊕U),rate,hn,hloss,hprob,?_,?_,hcost,hdeep⟩
  · intro σ hσ;exact hσ.2.2
  · exact mul_le_mul_of_nonneg_right hrate (by positivity)
end Oberwolfach
