module

public import Oberwolfach.OrdinaryRootFirstSharpReferencePerHostSafeSubsetQuantitative
public import Oberwolfach.OrdinaryTriangleFreshFromDeepParentInner
public import Oberwolfach.OrdinaryTriangleInnerSafeLikelyCertificate
public import Oberwolfach.OrdinaryTriangleInnerCertificateBudget

@[expose] public section
/-! A sharp root reference and the inner-domain parent yield a likely
triangle cover certificate, with the factor tolerance chosen before the
vortex scale. All cleanup and numerical inputs remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_sharp_reference_inner_certificate
    (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δref:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δref→δref<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀κe pmin bHub BHub:ℝ,0<κe→0<pmin→pmin≤1→0<bHub→0≤BHub→
    ∃εf ηhub ηend ζfresh εrows:ℝ,0<εf ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζfresh ∧ 0<εrows ∧
    ∀(b₀:ℕ) (p βe βh ν cap εsup δsample:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh)
      (hν:0<ν) (hcap:0<cap) (hsup:0<εsup) (hδsample:0<δsample),
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe βh ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧
    ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Ninner Nsafe:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nsafe≤Fintype.card (V⊕U)→
    ∀(loss:ℝ),0≤loss→loss≤1/8→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate b₁ c₁ deep crossLoss:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W 3 (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold:ℝ)
      (s:U→Color→ℝ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^1≤loss→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W 3 k (by decide)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₁ c₁ deep crossLoss D
      α ω βparent β b B h δref εparent εstar ηpack ξ ζ p ε f binner c)→
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→Disjoint Q F→
    βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U)→
    Ninner≤X.card→32≤X.card→16≤Fintype.card V→
    Fintype.card {v:V // v∉X}≤X.card^2→Fintype.card {u:U // u∉Z}≤X.card^2→
    OrdinaryDeepParentIngredients P Q F H X Z π d j s weight γold κold bold Bold εold ηend κe pmin
      pR pH density tR tH L Ledit βe₀ βh₀ δbal εrows tP K raw→
    OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub Q F H X Z→
    (∀v,F.degree v≤b₀)→L≤εf*X.card→
    ∀κscale:ℝ,OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν ηrate
      (p*ellrate+δsample) κscale ζfresh→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀rate cost deepCost:ℝ,ν+ηrate+4*p≤rate→ rate*Fintype.card (V⊕U)≤cost→
      rate*Fintype.card (V⊕U)≤deepCost→
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost:=by
  obtain ⟨N,hroot⟩:=ordinary_root_first_sharp_reference_per_host_safe_subset_quantitative 3 (by decide) α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δref hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hroot⟩:=hroot k hk ω β b B hpack δref hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
  obtain ⟨εf,ηhub,ηend,ζfresh,εrows,hεf,hηhub,hηend,hζfresh,hεrows,hfresh⟩:=
    ordinary_triangle_fresh_from_deep_parent_inner κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
  refine ⟨εf,ηhub,ηend,ζfresh,εrows,hεf,hηhub,hηend,hζfresh,hεrows,?_⟩
  intro b₀ p βe βh ν cap εsup δsample hp hp1 hβe hβh hν hcap hsup hδsample
  obtain ⟨Ninner,hfresh⟩:=hfresh b₀ p hp hp1 εsup hsup 1
  obtain ⟨Nsafe,hsafe⟩:=ordinary_triangle_inner_safe_likely_certificate p δsample hp hp1 hδsample
  obtain ⟨τ,hτeq,hτ,hτcap,hτone,hroot⟩:=hroot p βe βh ν cap hp hp1 hβe hβh hν hcap 1
  refine ⟨τ,hτeq,hτ,hτcap,hτone,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,hlinear,n₀,Nclean,hroot⟩:=hroot L hL
  refine ⟨ηpack,hηpack,hlinear,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,hroot⟩:=hroot ε hε
  refine ⟨Nreserve,Ninner,Nsafe,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnsafe loss hloss hloss8 P Q F H π d X T Z W
    ηrate ellrate b₁ c₁ deep crossLoss D βparent h εparent ξ ζ f binner c
    pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold s j weight raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hmE hmH hinner hX32 hV16 hJv hJu inputs hub hF hLfactor
    κscale hnum hbal hdiv rate cost deepCost hrate hcost hdeep
  let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)
  have hc:=hroot V U Γ Color hn loss hloss P Q F H π d X T Z W
    (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₁ c₁ deep crossLoss D
    βparent h εparent ξ ζ f binner c pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF inputs.conflict_degree inputs.profile hmE hmH
  have hc':1-(loss+2/(Fintype.card (V⊕U):ℝ)^1)≤
      law.probability (OrdinaryTriangleRootFirstSafeCleanupSample Q F H X T Z W
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p βe βh):=by
    dsimp [law,OrdinaryTriangleRootFirstSafeCleanupSample]
    exact hc
  have hf:=hfresh V U Γ Color P Q F H X Z π d j s weight γold κold bold Bold εold pR pH density
    tR tH tP L Ledit βe₀ βh₀ δbal K raw hinner hJv hJu inputs hub hF hLfactor
  have hc'' :1-(loss+2/(Fintype.card (V⊕U):ℝ))≤
      law.probability (OrdinaryTriangleRootFirstSafeCleanupSample Q F H X T Z W
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p βe βh):=by simpa only [pow_one] using hc'
  have hf':1-1/(X.card:ℝ)-1/(Fintype.card (V⊕U):ℝ)≤
      law.probability (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q X) F H
        (fun v u=>H v u∧v∈X∧u∈Z) X Z p ζfresh εsup):=by simpa only [pow_one] using hf
  have hbudget:=ordinary_triangle_inner_certificate_budget (U:=U) X loss hX32 hloss8
  exact hsafe V U Q F H X T Z W εsup τ ν ηrate ellrate κscale ζfresh βe βh
    (loss+2/(Fintype.card (V⊕U):ℝ)) rate cost deepCost D.toOrdinaryRootCoverData
    hnsafe hV16 (by omega) hbudget hnum hQF hbal hdiv hc'' hf' hrate hcost hdeep
end Oberwolfach
