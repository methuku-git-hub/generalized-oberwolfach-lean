module

public import Oberwolfach.OrdinaryTriangleSafeSampleFromInnerProbability
public import Oberwolfach.OrdinaryTriangleInnerLikelyCertificate

@[expose] public section
/-! The inner-scale fresh and safe cleanup probabilities give a likely
protected triangle cover certificate for the existing level-chain interface. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_inner_safe_likely_certificate
    (p δsample:ℝ) (hp:0<p) (hp1:p≤1) (hδ:0<δsample):∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (Q F:SimpleGraph V) (H:V→U→Prop) (A T:Finset V) (B W:Finset U)
      (εsup τ ν η ell κ ζ βe βh a rate cost deepCost:ℝ)
      (D:OrdinaryRootCoverData Q F H A T B W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))),
    N≤Fintype.card (V⊕U)→16≤Fintype.card V→0<A.card→a+1/(A.card:ℝ)≤1/4→
    OrdinaryTriangleRootFirstScaledConditions Q H A B p εsup τ ν η (p*ell+δsample) κ ζ→
    Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-a≤law.probability (OrdinaryTriangleRootFirstSafeCleanupSample Q F H A T B W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh)→
    1-1/(A.card:ℝ)-1/(Fintype.card (V⊕U):ℝ)≤
      law.probability (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
        (fun v u=>H v u∧v∈A∧u∈B) A B p ζ εsup)→
    ν+η+4*p≤rate→ rate*Fintype.card (V⊕U)≤cost→ rate*Fintype.card (V⊕U)≤deepCost→
    OrdinaryTriangleLikelyCoverCertificate Q F H A T B W cost deepCost:=by
  obtain ⟨N,hN⟩:=ordinary_triangle_safe_sample_from_inner_probability p δsample hp hp1 hδ 1
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H A T B W εsup τ ν η ell κ ζ βe βh a rate cost deepCost D
    hn hn16 hA hloss hnum hQF hbal hdiv law hclean hfresh hrate hcost hdeep
  have hfresh':1-1/(A.card:ℝ)^1-1/(Fintype.card (V⊕U):ℝ)^1≤
      law.probability (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
        (fun v u=>H v u∧v∈A∧u∈B) A B p ζ εsup):=by simpa only [pow_one] using hfresh
  have hprob:=hN V U Q F H A T B W εsup τ ν η ell κ ζ βe βh a D hn hnum hQF hbal hdiv hclean hfresh'
  simp only [pow_one] at hprob
  let E:=fun σ=>OrdinaryTriangleRootFirstSafeCleanupSample Q F H A T B W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
    OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
      (fun v u=>H v u∧v∈A∧u∈B) A B p ζ εsup σ ∧
    OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ ∧
    OrdinaryProtectedHostCoverDownResult Q F H A T B W 3
      ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))
  have hlocal:(ν+η+4*p)*Fintype.card (V⊕U)≤rate*Fintype.card (V⊕U):=
    mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)
  exact ordinary_triangle_inner_likely_certificate Q F H A T B W law E a
    ((ν+η+4*p)*Fintype.card (V⊕U)) rate cost deepCost hn16 hA hloss hprob
    (fun σ hσ=>hσ.2.2.2) hlocal hcost hdeep
end Oberwolfach
