module

public import Oberwolfach.OrdinaryTriangleReferenceThenFreshOrderedRatesQuantitative
public import Oberwolfach.OrdinaryTriangleOrderedReferenceCertificate
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

theorem ordinary_triangle_reference_then_fresh_ordered_certificate_quantitative
    (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀γ κ bFactor BFactor:ℝ,0<γ→0<κ→0<bFactor→0≤BFactor→
    ∃εf ηf ζfresh:ℝ,0<εf ∧ 0<ηf ∧ 0<ζfresh ∧
    ∀(rate pcap othercap:ℝ),0<rate→0<pcap→0<othercap→
    ∃p εsup cap:ℝ,∃(hp:0<p) (hp1:p≤1),p≤pcap ∧ 0<εsup ∧ 0<cap ∧ cap≤othercap ∧
    ∃Norder:ℕ,∀(βe βh ν:ℝ),0<βe→0<βh→0<ν→ν≤cap→
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe βh ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧ ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
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
    ∀cost deepCost:ℝ,rate*Fintype.card (V⊕U)≤cost→ rate*Fintype.card (V⊕U)≤deepCost→
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost :=by
  obtain ⟨N,hcombined⟩:=ordinary_triangle_reference_then_fresh_ordered_rates_quantitative α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hcombined⟩:=hcombined k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro γ κ bFactor BFactor hγ hκ hbFactor hBFactor
  obtain ⟨εf,ηf,ζfresh,hεf,hηf,hζfresh,hcombined⟩:=hcombined γ κ bFactor BFactor hγ hκ hbFactor hBFactor
  refine ⟨εf,ηf,ζfresh,hεf,hηf,hζfresh,?_⟩
  intro rate pcap othercap hrate hpcap hother
  obtain ⟨p,εsup,cap,hp,hp1,hpcap',hsup,hcap,hothercap,Norder,hcombined⟩:=hcombined rate pcap othercap hrate hpcap hother
  refine ⟨p,εsup,cap,hp,hp1,hpcap',hsup,hcap,hothercap,Norder,?_⟩
  intro βe βh ν hβe hβh hν hνcap
  obtain ⟨τ,hτeq,hτ,hτcap,hτone,hcombined⟩:=hcombined βe βh ν hβe hβh hν hνcap 1
  refine ⟨τ,hτeq,hτ,hτcap,hτone,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,hlinear,n₀,Nclean,hcombined⟩:=hcombined L hL
  refine ⟨ηpack,hηpack,hlinear,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,Nfresh,hcombined⟩:=hcombined ε hε
  refine ⟨Nreserve,Nfresh,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnFresh hnOrder hu hn16 loss hloss hlossSmall
    P Q Qfactor F H Hfactor π d X T Z W ηrate ellrate b₀ c₀ D βparent h εparent ξ ζ f binner c
    pR pH density tR tH Ledit βe₀ βh₀ s j raw hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH data
    hηrate hellrate hηcap hellcap hbal hdiv hbase cost deepCost hcost hdeep
  have hprob:=hcombined V U Γ Color hn hnFresh hnOrder hu loss hloss P Q Qfactor F H Hfactor π d X T Z W
    ηrate ellrate b₀ c₀ D βparent h εparent ξ ζ f binner c pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH data
    hηrate hellrate hηcap hellcap hbal hdiv hbase
  simp only [pow_one] at hprob
  exact ordinary_triangle_ordered_reference_certificate Q Qfactor F H Hfactor X T Z W
    p εsup τ ν ηrate ellrate ζfresh βe βh loss rate cost deepCost D.toOrdinaryRootCoverData
    (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1))
    hn16 hlossSmall hcost hdeep hprob
end Oberwolfach
