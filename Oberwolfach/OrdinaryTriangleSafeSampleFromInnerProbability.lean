module

public import Oberwolfach.OrdinaryTriangleRootFirstSafeSampleEventSampledCover
public import Oberwolfach.OrdinarySampledCoverDegree
public import Oberwolfach.OrdinaryPhysicalInnerHost

@[expose] public section
/-! Combine the inner-scale fresh event, safe cleanup and the sampled cover
on the same fresh coins, obtaining the protected triangle cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_safe_sample_from_inner_probability
    (p δsample:ℝ) (hp:0<p) (hp1:p≤1) (hδ:0<δsample) (q:ℕ):∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (Q F:SimpleGraph V) (H:V→U→Prop) (A T:Finset V) (B W:Finset U)
      (εsup τ ν η ell κ ζ βe βh a:ℝ)
      (D:OrdinaryRootCoverData Q F H A T B W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))),
    N≤Fintype.card (V⊕U)→
    OrdinaryTriangleRootFirstScaledConditions Q H A B p εsup τ ν η (p*ell+δsample) κ ζ→
    Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-a≤law.probability (OrdinaryTriangleRootFirstSafeCleanupSample Q F H A T B W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh)→
    1-1/(A.card:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      law.probability (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
        (fun v u=>H v u∧v∈A∧u∈B) A B p ζ εsup)→
    1-a-(1/(A.card:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)-1/(Fintype.card (V⊕U):ℝ)^q≤
      law.probability (fun σ=>
        OrdinaryTriangleRootFirstSafeCleanupSample Q F H A T B W
          (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
          (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
        OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
          (fun v u=>H v u∧v∈A∧u∈B) A B p ζ εsup σ ∧
        OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ ∧
        OrdinaryProtectedHostCoverDownResult Q F H A T B W 3
          ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=ordinary_sampled_cover_degree_high_probability p δsample hp.le hp1 hδ q
  refine ⟨N,?_⟩
  intro V U _ _ _ _ Q F H A T B W εsup τ ν η ell κ ζ βe βh a D hn hnum hQF hbal hdiv law hclean hfresh
  have hcover:=hN V U hn (ordinaryPhysicalGraph D.rim D.spokes)
  have hbase:ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B)≤
      spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices A B):=le_of_eq (ordinary_physical_inner_host Q H A B)
  have hfresh':1-(1/(A.card:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤
      law.probability (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
        (fun v u=>H v u∧v∈A∧u∈B) A B p ζ εsup):=by linarith only [hfresh]
  exact ordinary_triangle_root_first_safe_same_sample_event_sampled_cover Q (spanningRestriction Q A) F H
    (fun v u=>H v u∧v∈A∧u∈B) A T B W p εsup τ ν η ell κ ζ βe βh δsample D hnum
    hQF hbal hdiv hbase law a (1/(A.card:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q) hclean hfresh'
    (1/(Fintype.card (V⊕U):ℝ)^q) hcover
end Oberwolfach
