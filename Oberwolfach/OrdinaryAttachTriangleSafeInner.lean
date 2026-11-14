module

public import Oberwolfach.OrdinaryTriangleSafeSampleFromInnerProbability
public import Oberwolfach.FiniteLawAttachConditionalEvent

@[expose] public section
/-! The protected triangle cover-down can be attached to an arbitrary
prior on the earlier outcome and the same fresh physical-edge coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attach_triangle_safe_inner
    (p δsample:ℝ) (hp:0<p) (hp1:p≤1) (hδ:0<δsample) (q:ℕ):∃N:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U],
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (prior:(Σ _:Ω,Sym2 (V⊕U)→Bool)→Prop)
      (Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (A T:Ω→Finset V) (B W:Ω→Finset U)
      (εsup τ ν η ell κ ζ βe βh a e:ℝ) (M:ℕ)
      (D:∀ω,OrdinaryRootCoverData (Q ω) (F ω) (H ω) (A ω) (T ω) (B ω) (W ω) 3
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))),
    N≤Fintype.card (V⊕U)→0<M→0≤a→
    (∀ω,E ω→M≤(A ω).card)→
    (∀ω,E ω→OrdinaryTriangleRootFirstScaledConditions (Q ω) (H ω) (A ω) (B ω)
      p εsup τ ν η (p*ell+δsample) κ ζ)→
    (∀ω,E ω→Disjoint (Q ω) (F ω))→
    (∀ω,E ω→∀v,(Q ω).degree v=2*(Finset.univ.filter (H ω v)).card)→
    (∀ω,E ω→∀u,3∣(Finset.univ.filter (fun v=>H ω v u)).card)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    (∀ω,E ω→1-a≤law.probability (OrdinaryTriangleRootFirstSafeCleanupSample
      (Q ω) (F ω) (H ω) (A ω) (T ω) (B ω) (W ω)
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) (D ω) p βe βh))→
    (∀ω,E ω→1-1/((A ω).card:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      law.probability (OrdinaryTriangleFreshFactorSample (Q ω) (spanningRestriction (Q ω) (A ω)) (F ω) (H ω)
        (fun v u=>H ω v u∧v∈A ω∧u∈B ω) (A ω) (B ω) p ζ εsup))→
    1-e≤(μ.sigma (fun _=>law)).probability prior→(∀z,prior z→E z.1)→
    1-(e+(a+3/(M:ℝ)^q))≤(μ.sigma (fun _=>law)).probability (fun z=>prior z ∧
      OrdinaryTriangleRootFirstSafeCleanupSample (Q z.1) (F z.1) (H z.1) (A z.1) (T z.1) (B z.1) (W z.1)
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) (D z.1) p βe βh z.2 ∧
      OrdinaryTriangleFreshFactorSample (Q z.1) (spanningRestriction (Q z.1) (A z.1)) (F z.1) (H z.1)
        (fun v u=>H z.1 v u∧v∈A z.1∧u∈B z.1) (A z.1) (B z.1) p ζ εsup z.2 ∧
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph (D z.1).rim (D z.1).spokes) p δsample z.2 ∧
      OrdinaryProtectedHostCoverDownResult (Q z.1) (F z.1) (H z.1) (A z.1) (T z.1) (B z.1) (W z.1) 3
        ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))):=by
  obtain ⟨N,hN⟩:=ordinary_triangle_safe_sample_from_inner_probability p δsample hp hp1 hδ q
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ μ E prior Q F H A T B W εsup τ ν η ell κ ζ βe βh a e M D hn hM ha
    hsize hnum hQF hbal hdiv law hclean hfresh hprior hpriorE
  let Good:=fun ω σ=>
    OrdinaryTriangleRootFirstSafeCleanupSample (Q ω) (F ω) (H ω) (A ω) (T ω) (B ω) (W ω)
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) (D ω) p βe βh σ ∧
    OrdinaryTriangleFreshFactorSample (Q ω) (spanningRestriction (Q ω) (A ω)) (F ω) (H ω)
      (fun v u=>H ω v u∧v∈A ω∧u∈B ω) (A ω) (B ω) p ζ εsup σ ∧
    OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph (D ω).rim (D ω).spokes) p δsample σ ∧
    OrdinaryProtectedHostCoverDownResult (Q ω) (F ω) (H ω) (A ω) (T ω) (B ω) (W ω) 3
      ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))
  have hMr:0<(M:ℝ):=Nat.cast_pos.mpr hM
  have hgood:∀ω,E ω→1-(a+3/(M:ℝ)^q)≤law.probability (Good ω):=by
    intro ω hω
    have hA:M≤(A ω).card:=hsize ω hω
    have hAV:(A ω).card≤Fintype.card V:=Finset.card_le_univ (A ω)
    have hVW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    have fA:1/((A ω).card:ℝ)^q≤1/(M:ℝ)^q:=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hMr _) (pow_le_pow_left₀ hMr.le (Nat.cast_le.mpr hA) _)
    have fW:1/(Fintype.card (V⊕U):ℝ)^q≤1/(M:ℝ)^q:=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hMr _)
        (pow_le_pow_left₀ hMr.le (Nat.cast_le.mpr (hA.trans (hAV.trans hVW))) _)
    have hh:=hN V U (Q ω) (F ω) (H ω) (A ω) (T ω) (B ω) (W ω) εsup τ ν η ell κ ζ βe βh a
      (D ω) hn (hnum ω hω) (hQF ω hω) (hbal ω hω) (hdiv ω hω) (hclean ω hω) (hfresh ω hω)
    change 1-a-(1/((A ω).card:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)-1/(Fintype.card (V⊕U):ℝ)^q≤
      law.probability (Good ω) at hh
    have heq:3/(M:ℝ)^q=3*(1/(M:ℝ)^q):=by ring
    linarith only [hh,fA,fW,heq]
  have hcost:0≤a+3/(M:ℝ)^q:=by positivity
  exact finiteLaw_attach_conditional_event μ (fun _=>law) E prior Good e _ hcost hprior hpriorE hgood
end Oberwolfach
