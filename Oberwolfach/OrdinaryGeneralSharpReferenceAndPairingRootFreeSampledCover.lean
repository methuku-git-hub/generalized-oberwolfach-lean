module

public import Oberwolfach.OrdinaryGeneralRootFreeSampledCoverCleanupSubsetProbability
public import Oberwolfach.OrdinaryRootFirstRootFreeSharpReferencePerHostSampledCover
public import Oberwolfach.OrdinaryGeneralSampleFromPairingParentRootFreeSampledCover

@[expose] public section
/-! The root-cover reference and an actual pairing parent give a single
    fresh sample with cleanup, pairing and protected general-wheel finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_sharp_reference_and_pairing_root_free_sampled_cover
    (m:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀(γ κ bFactor BFactor p₀ a εf ηf ζfresh:ℝ),
    OrdinaryGeneralFreshPairingProbabilityProperty m γ κ bFactor BFactor p₀ a εf ηf ζfresh→
    ∀(b₀:ℕ) (p βe βh ν cap εsup ρ:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh)
      (hν:0<ν) (hcap:0<cap) (hsup:0<εsup) (hρ:0<ρ) (δsample:ℝ) (hδsample:0<δsample) (q:ℕ),
    ∃τ:ℝ,τ=ordinarySafeCleanupScale (m+1) p βe (βh/2) ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧ ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Nfresh:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nfresh≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(loss:ℝ),0≤loss→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηcover ell bin cin deep crossLoss:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) ηcover ell)
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^q≤loss→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega) ηcover ell bin cin deep crossLoss D
      α ω βparent β b B h δ εparent εstar ηpack ξ ζ p ε f binner cross)→
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→
    (W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max ηcover ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    ∀(tw:{v:V // v∉X}→ℝ),
    MixedFreshPairingParentInsideRoots m b₀ γ κ bFactor BFactor p₀ a εf ηf Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr) tw→
    ∀budget deepBudget:ℝ,ηcover≤deepBudget→0≤τ→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    (∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) ηcover ell
      (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ→
      OrdinaryGeneralRootFirstSampledCoverMargins m Q Qfactor F H Hfactor X T Z W ηcover ell
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData σ O p ρ ζfresh εsup (βe/2) budget
        (p*ell+δsample*Fintype.card (V⊕U)))→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)-
      (1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W ηcover ell
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p (βe/2) βh δsample σ ∧
      OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζfresh εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget deepBudget) :=by
  obtain ⟨N,hroot⟩:=ordinary_root_first_root_free_sharp_reference_per_host_sampled_cover (m+1) (by omega) α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hroot⟩:=hroot k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro γ κ bFactor BFactor p₀ a εf ηf ζfresh hfresh b₀ p βe βh ν cap εsup ρ hp hp1 hβe hβh hν hcap hsup hρ δsample hδsample q
  obtain ⟨Nfresh,hpair⟩:=ordinary_general_sample_from_pairing_parent_root_free_sampled_cover m b₀ hm γ κ bFactor BFactor p₀ a εf ηf ζfresh
    hfresh p hp hp1 ρ hρ εsup hsup q
  obtain ⟨τ,hτeq,hτ,hτcap,hτone,hroot⟩:=hroot p βe βh ν cap hp hp1 hβe hβh hν hcap δsample hδsample q
  refine ⟨τ,hτeq,hτ,hτcap,hτone,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,hlinear,n₀,Nclean,hroot⟩:=hroot L hL
  refine ⟨ηpack,hηpack,hlinear,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,hroot⟩:=hroot ε hε
  refine ⟨Nreserve,Nfresh,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnFresh hu loss hloss P Q Qfactor F H Hfactor π d X T Z W ηcover ell bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hW hQF hF hprofile hmE hmH tw data budget deepBudget hdeep hτ0 hbal hdiv hnum law
  have hc:=hroot V U Γ Color hn loss hloss P Q F H π d X T Z W ηcover ell bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hW hQF hF hprofile hmE hmH
  have hc':1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)≤
      law.probability (OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W ηcover ell
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p (βe/2) βh δsample):=by
    exact ordinary_general_root_free_sampled_cover_cleanup_subset_probability m Q F H X T Z W ηcover ell
      (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p (βe/2) βh δsample
      (1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)) law hc
  have hmE':(βe/2)*Fintype.card (V⊕U)+3*max ηcover ell≤βe₀*Fintype.card (V⊕U):=by
    have hn0:(0:ℝ)≤Fintype.card (V⊕U):=by positivity
    nlinarith [hβe]
  exact hpair V U Γ Color hnFresh hu P Q Qfactor F H Hfactor π d X T Z W ηcover ell
    (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData tw data
    pR pH density tR tH Ledit βe₀ βh₀ (βe/2) βh budget deepBudget (loss+2/(Fintype.card (V⊕U):ℝ)^q) δsample s j raw
    (by positivity) hQF hbal hdiv hprofile hmE' hmH hnum (by linarith [hdeep]) hc'
end Oberwolfach
