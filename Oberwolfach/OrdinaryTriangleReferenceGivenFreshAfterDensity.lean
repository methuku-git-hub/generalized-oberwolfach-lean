module

public import Oberwolfach.OrdinaryTriangleReferenceGivenFreshProbability
public import Oberwolfach.OrdinaryRootFirstRatesAfterDensity

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

theorem ordinary_triangle_reference_and_given_fresh_after_density
    (α γ κ bFactor BFactor εf ηf ζfresh:ℝ) (hα:0<α) (hγ:0<γ) (hκ:0<κ) (hζfresh:0<ζfresh)
    (hfresh:OrdinaryTriangleFreshFactorProbabilityProperty γ κ bFactor BFactor εf ηf ζfresh):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧
    ∀(rate pcap othercap:ℝ),0<rate→0<pcap→0<othercap→
    ∃pbound:ℝ,0<pbound ∧ pbound≤pcap ∧
    ∀(p:ℝ) (hp:0<p),p≤pbound→∃εsup cap:ℝ,∃(hp1:p≤1),0<εsup ∧ 0<cap ∧ cap≤othercap ∧
    ∃Norder:ℕ,∀(βe βh ν:ℝ),0<βe→0<βh→0<ν→ν≤cap→∀q:ℕ,
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Nfresh:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nfresh≤Fintype.card V→Norder≤Fintype.card (V⊕U)→Fintype.card U≤Fintype.card V→
    ∀(loss:ℝ),0≤loss→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate b₀ c₀:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W 3 (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^q≤loss→
    Nonempty (OrdinaryRootCoverReferenceData P Q F H X T Z W 3 k (by decide)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₀ c₀ D
      α ω βparent β b B h δ εparent εstar ηpack ξ ζ p ε f binner c)→
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
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)-
      (1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      OrdinaryTriangleRootFirstCleanupSample Q F H X T Z W
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p βe βh σ ∧
      OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζfresh εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
        ((ν+ηrate+4*p)*Fintype.card (V⊕U)) ((ν+ηrate+4*p)*Fintype.card (V⊕U)) ∧
      ν+ηrate+4*p≤rate) :=by
  obtain ⟨N,hcombined⟩:=ordinary_triangle_reference_and_given_fresh_probability α γ κ bFactor BFactor εf ηf ζfresh hα hγ hκ hζfresh hfresh
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,hεstar,hcombined⟩:=hcombined k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,hεstar,?_⟩
  intro rate pcap othercap hrate hpcap hother
  have hκ':0<min (κ/2) γ:=lt_min (by positivity) hγ
  obtain ⟨pbound,hpbound,hpboundcap,hrates⟩:=
    ordinary_root_first_rates_after_density (min (κ/2) γ) ζfresh rate pcap othercap hκ' hζfresh hrate hpcap hother
  refine ⟨pbound,hpbound,hpboundcap,?_⟩
  intro p hp hpbound'
  obtain ⟨εsup,cap,hp1,hpκ,hsqrt,hsup,hεsup,hcap,hothercap,hrates,Norder,horder⟩:=hrates p hp hpbound'
  refine ⟨εsup,cap,hp1,hsup,hcap,hothercap,Norder,?_⟩
  intro βe βh ν hβe hβh hν hνcap q
  obtain ⟨τ,hτ,hτcap,hcombined⟩:=hcombined p βe βh ν cap εsup hp hp1 hβe hβh hν hcap hsup q
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,n₀,Nclean,hcombined⟩:=hcombined L hL
  refine ⟨ηpack,hηpack,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,Nfresh,hcombined⟩:=hcombined ε hε
  refine ⟨Nreserve,Nfresh,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnFresh hnOrder hu loss hloss P Q Qfactor F H Hfactor π d X T Z W
    ηrate ellrate b₀ c₀ D βparent h εparent ξ ζ f binner c pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH data hηrate hellrate hηcap hellcap
    hbal hdiv hbase law
  obtain ⟨hsupport,hclass,hblock,hcost⟩:=hrates τ ν ηrate ellrate hτ.le hν.le hηrate hellrate hτcap hνcap hηcap hellcap
  have hh:=hcombined V U Γ Color hn hnFresh hu loss hloss P Q Qfactor F H Hfactor π d X T Z W
    ηrate ellrate b₀ c₀ D βparent h εparent ξ ζ f binner c pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH data
    hεsup hsupport hclass hblock hpκ hsqrt (horder _ hnOrder) hbal hdiv hbase
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.1,hσ.2.1,hσ.2.2,hcost⟩
end Oberwolfach
