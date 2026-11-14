module

public import Oberwolfach.OrdinaryTriangleDeepSharpFreshBeforeSpacing
public import Oberwolfach.OrdinaryVortexRootStaticGeometryRateMonotone

@[expose] public section
/-! Choose the certificate retention rate below the preselected geometry
cap, and select geometry at a tolerance fixed before the conflict size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleSharpFreshAfterCleanup
    (α:ℝ) (k:ℕ) (ω β b B hpack δ εstar cLinear γ κ bFactor BFactor εf ηf ζfresh:ℝ)
    (Norder:ℕ) (rate p εsup cap βe βh ν τ:ℝ):Prop :=
    ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Nfresh:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nfresh≤Fintype.card V→Norder≤Fintype.card (V⊕U)→Fintype.card U≤Fintype.card V→16≤Fintype.card V→
    ∀(loss:ℝ),0≤loss→loss≤1/4→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate b₀ c₀ deep crossLoss:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W 3 (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^1≤loss→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W 3 k (by decide)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₀ c₀ deep crossLoss D
      α ω βparent β b B h δ εparent εstar ηpack ξ ζ p ε f binner c)→
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→
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
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost

theorem ordinary_triangle_sharp_geometry_rate_alignment
    (α:ℝ) (k:ℕ) (ω β b B hpack δ εstar cLinear γ κ bFactor BFactor εf ηf ζfresh:ℝ)
    (hlinear:0<cLinear)
    (hfamily:OrdinaryTriangleSharpFreshAfterChoice α k ω β b B hpack δ εstar cLinear γ κ bFactor BFactor εf ηf ζfresh)
    (ρ₀ βparent εparent gap ξ ζ edit:ℝ)
    (hgeometry:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
        OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap β ξ ζ edit p η eps γgeo)
    (rate pcap othercap:ℝ) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃p εsup cap:ℝ,∃(hp:0<p) (hp1:p≤1),p≤pcap ∧ 0<εsup ∧ 0<cap ∧ cap≤othercap ∧
    ∃Norder:ℕ,∀(βe βh ν:ℝ),0<βe→0<βh→0<ν→ν≤cap→
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe βh ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧
    ∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap β ξ ζ edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleSharpFreshAfterCleanup α k ω β b B hpack δ εstar cLinear γ κ bFactor BFactor εf ηf ζfresh
        Norder rate p εsup cap βe βh ν τ :=by
  obtain ⟨pGeo,hpGeo,hpGeo1,hpGeoCap,hgeo⟩:=hgeometry pcap hpcap
  obtain ⟨p,εsup,cap,hp,hp1,hpSmall,hεsup,hcap,hcapOther,Norder,hfamily⟩:=
    hfamily rate pGeo othercap hrate hpGeo hother
  refine ⟨p,εsup,cap,hp,hp1,hpSmall.trans hpGeoCap,hεsup,hcap,hcapOther,Norder,?_⟩
  intro βe βh ν hβe hβh hν hνcap
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hcleanup⟩:=hfamily βe βh ν hβe hβh hν hνcap
  obtain ⟨eps,γgeo,heps,heps1,hγgeo,hgeo⟩:=hgeo (cLinear*τ) (by positivity)
  have hgeo':=ordinary_vortex_buffered_root_static_geometry_sampling_rate_mono 3 k 2 ρ₀ βparent b B εparent gap
    β ξ ζ edit pGeo p (cLinear*τ) eps γgeo hp.le hpSmall hgeo
  exact ⟨τ,hτeq,hτ,hτcap,hτ1,eps,γgeo,heps,heps1,hγgeo,hgeo',hcleanup⟩
end Oberwolfach
