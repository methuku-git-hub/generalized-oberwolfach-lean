module

public import Oberwolfach.OrdinaryTriangleFixedMarginPairedSampleReference
public import Oberwolfach.OrdinaryTriangleOriginalMarginPairedSampleReference
public import Oberwolfach.OrdinaryTriangleReferencePackingMargin
public import Oberwolfach.OrdinaryTrianglePairedSampleProperty
public import Oberwolfach.OrdinaryTriangleOriginalMarginPairedReference
public import Oberwolfach.OrdinaryTriangleReferenceSubmargin
public import Oberwolfach.OrdinaryTriangleVortexPairedHostReferenceCuts
public import Oberwolfach.OrdinaryTriangleVortexJointHostReferenceCuts
public import Oberwolfach.OrdinaryTriangleVortexJointSelectedHostReference
public import Oberwolfach.OrdinaryReferenceCutsDomainSelectorChoice
public import Oberwolfach.OrdinaryTriangleVortexJointHostReferenceCertificate
public import Oberwolfach.OrdinaryNondeeperTriangleToleranceChoice
public import Oberwolfach.OrdinaryTriangleVortexJointReferenceCertificate
public import Oberwolfach.OrdinaryTriangleFixedDomainSelectorChoice
public import Oberwolfach.OrdinaryTriangleDeepParentJointReferenceCertificate
public import Oberwolfach.OrdinaryTriangleDeepParentOrderedCertificate
public import Oberwolfach.OrdinaryTriangleParentRootScaleChoiceAnchored
public import Oberwolfach.OrdinaryDeepParentEarlyWeightsHierarchy
public import Oberwolfach.OrdinaryTriangleReferenceFreshOrderedCertificate
public import Oberwolfach.OrdinaryRootFirstTraceRatesMonotone

@[expose] public section
/-! A root-cover reference and a mixed-factor parent yield the cleanup,
    post-cover tests and protected triangle cover-down on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fixed_margin_packing_sample_reference
    (pmin κe a K bcap Bmin α ρ₀ pstar:ℝ) (hpmin:0<pmin) (hκe:0<κe) (ha:0<a) (hK:0<K)
    (hbcap:0<bcap) (hBmin:0≤Bmin) (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1)
    (hθ1:max (1/2) (cycleThreshold 3)+α/4≤1):
    ∃γ κ bFactor BFactor:ℝ,0<γ ∧ 0<κ ∧ 0<bFactor ∧ bFactor≤bcap ∧ 0<BFactor ∧ Bmin≤BFactor ∧
    ∃δ href:ℝ,0<δ ∧ δ<1/8 ∧ 0<href ∧
      (∀(η χ Lconf:ℝ),0<η→η<1→0<χ→0≤Lconf→∀d:ℕ,∀hd:2≤d,∃M:ℕ,1≤M ∧
        OrdinaryReferenceCutsDomainSelector d M hd (α/2) pstar (ρ₀/16) (2*δ) href η χ Lconf) ∧
    (∀ζroot ξ ζ:ℝ,ζroot≤href→ξ+ζ≤href/2→href/4≤(2*href-ζroot)-ξ-ζ) ∧
    ∃βP:ℝ,0<βP ∧
      (∀εTri:ℝ,0<εTri→∃βmax:ℝ,0<βmax ∧ βmax≤1/4 ∧ βmax≤α/8 ∧ βmax≤εTri) ∧
    ∀(d:ℕ) (hd:2≤d) (ηP:ℝ),0<ηP→
    ∃(k:ℕ) (βH cParent Bparent:ℝ),5≤k ∧ 0<βH ∧ 0<cParent ∧ 0<Bparent ∧
    (∀ηH η χhost χcut:ℝ,0<ηH→0<η→η<1→0<χhost→0<χcut→
      OrdinaryTrianglePairedSampleProperty k d hd α ρ₀ pstar βP ηP ηH βH cParent Bparent
        η χhost (2*δ) href χcut hpstar) ∧
    ∀β:ℝ,0<β→
    let hpack:=href/4;let ω:=ρ₀/16;
    ∃εstar:ℝ,0<εstar ∧ ∃εf ηf ζfresh:ℝ,0<εf ∧ 0<ηf ∧ 0<ζfresh ∧
    ∃δDeep εDeep tDeep lamDeep:ℝ,
      OrdinaryDeepNumericParameters pmin κe a ηf εf K γ κ δDeep εDeep tDeep lamDeep bFactor BFactor ∧
    ∀ηH gap ζcap:ℝ,0<ηH→0<gap→0<ζcap→ζcap≤href→
    ∃ζRoot rateRoot lamRoot:ℝ,0<ζRoot ∧ 0<rateRoot ∧ 0<lamRoot ∧ ζRoot≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent ω pstar (βH/2) (2*ηH) ζRoot rateRoot N₀ ∧
      OrdinaryUniformRootReferenceAtScale 3 (by omega) k (α/2) (βH/2) cParent (Bparent/(ω*pstar^(2*3-1)))
        (2*href-ζRoot) (2*δ) (2*ηH) ω gap lamRoot ∧
    ∀(rate pcap othercap:ℝ),0<rate→0<pcap→0<othercap→
    ∃p εsup cap:ℝ,∃(hp:0<p) (hp1:p≤1),p≤pcap ∧ 0<εsup ∧ 0<cap ∧ cap≤othercap ∧
    ∃Norder:ℕ,∀(βe βh ν:ℝ),0<βe→0<βh→0<ν→ν≤cap→
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Nfresh:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nfresh≤Fintype.card V→Norder≤Fintype.card (V⊕U)→Fintype.card U≤Fintype.card V→16≤Fintype.card V→
    ∀(loss:ℝ),0≤loss→loss≤1/4→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate b₀ c₀:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W 3 (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^1≤loss→
    Nonempty (OrdinaryRootCoverReferenceData P Q F H X T Z W 3 k (by decide)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₀ c₀ D
      (α/2) ω βparent β (cParent*(1-2*δ)^((3:ℕ)-1)) (Bparent/(ω*pstar^(2*3-1))) h δ εparent εstar ηpack ξ ζ p ε f binner c)→
    (T.card:ℝ)≤((p^3*βe/2)/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U)→
    ∀(data:MixedFreshParentDataInsideRoots γ κ bFactor BFactor εf ηf Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)),
    0≤ηrate→0≤ellrate→ηrate≤cap→ellrate≤cap→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)→
    ∀cost deepCost:ℝ,rate*Fintype.card (V⊕U)≤cost→ rate*Fintype.card (V⊕U)≤deepCost→
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost :=by
  obtain ⟨γ,κ,bFactor,BFactor,hγ,hκ,hbFactor,hbcap',hBFactor,hBmin',δ,href,hδ,hδ1,hhref,hcuts,βP,hβP,hgeo,hcombined⟩:=
    ordinary_triangle_fixed_margin_paired_sample_reference pmin κe a K bcap Bmin α ρ₀ pstar
      hpmin hκe ha hK hbcap hBmin hα hα1 hρ₀ hpstar hpstar1 hθ1
  refine ⟨γ,κ,bFactor,BFactor,hγ,hκ,hbFactor,hbcap',hBFactor,hBmin',δ,href,hδ,hδ1,hhref,hcuts,?_,βP,hβP,hgeo,?_⟩
  · intro ζroot ξ ζ hroot hloss
    linarith
  · intro d hd ηP hηP
    obtain ⟨k,βH,cParent,Bparent,hk,hβH,hc,hB,hsample,hcombined⟩:=hcombined d hd ηP hηP
    refine ⟨k,βH,cParent,Bparent,hk,hβH,hc,hB,hsample,?_⟩
    intro β hβ hpack ω
    exact hcombined β (href/4) hβ (by positivity)
end Oberwolfach
