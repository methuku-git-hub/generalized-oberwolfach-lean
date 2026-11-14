module

public import Oberwolfach.OrdinaryTriangleSharpInnerFamilyBeforeSpacing
public import Oberwolfach.OrdinaryVortexRootStaticGeometryRateMonotone
public import Oberwolfach.OrdinaryRootFirstTraceRatesMonotone

@[expose] public section
/-! Synchronize the triangle inner certificate and buffered geometry before
choosing the conflict bound, with one retention rate and cleanup scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleSharpInnerAfterCleanup
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ):Prop :=
    ∀(b₀:ℕ) (L:ℝ),0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
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
    OrdinaryTriangleLikelyCoverCertificate Q F H X T Z W cost deepCost

theorem ordinary_triangle_sharp_inner_rate_geometry_alignment
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (hlinear:0<cLinear) (hζfresh:0<ζfresh)
    (hfamily:OrdinaryTriangleSharpInnerAfterChoice α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows)
    (ρ₀ βparent εparent gap ξ ζ edit:ℝ)
    (hgeometry:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
        OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap β ξ ζ edit p η eps γgeo)
    (κscale rate pcap othercap:ℝ) (hκscale:0<κscale) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃p εsup capSmall δsample ν:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζfresh*κscale ∧ 20*Real.sqrt (2*p)≤ζfresh*κscale/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<capSmall ∧ capSmall≤othercap ∧ 0<δsample ∧ 0<ν ∧ ν≤capSmall ∧
    ∃Norder:ℕ,(∀n:ℕ,Norder≤n→2≤ζfresh*κscale*p*n/4) ∧
    ∀βe βh:ℝ,0<βe→0<βh→
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe βh ν (min capSmall 1) ∧ 0<τ ∧ τ≤capSmall ∧ τ≤1 ∧
    (∀η ell:ℝ,0≤η→0≤ell→η≤capSmall→ell≤capSmall→
      τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤ζfresh*κscale*p/4 ∧ ν+η≤ζfresh*κscale*p/4 ∧ ν+η+4*p≤rate) ∧
    ∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap β ξ ζ edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleSharpInnerAfterCleanup α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ :=by
  obtain ⟨pGeo,hpGeo,hpGeo1,hpGeoCap,hgeo⟩:=hgeometry pcap hpcap
  obtain ⟨p,εsup,cap,hp,hp1,hpSmall,hpκ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hRates,Norder,hOrder⟩:=
    ordinary_root_first_trace_rates_monotone κscale ζfresh rate pGeo othercap hκscale hζfresh hrate hpGeo hother
  let capSmall:ℝ:=cap/4
  have hc:0<capSmall:=by dsimp [capSmall];positivity
  have hcCap:capSmall≤cap:=by dsimp [capSmall];linarith
  refine ⟨p,εsup,capSmall,capSmall,capSmall,hp,hp1,hpSmall.trans hpGeoCap,hpκ,hsqrt,
    hεsup,hεsupCap,hc,hcCap.trans hcapOther,hc,hc,le_rfl,Norder,hOrder,?_⟩
  intro βe βh hβe hβh
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hcleanup⟩:=hfamily p βe βh capSmall capSmall εsup capSmall
    hp hp1 hβe hβh hc hc hεsup hc
  have hnum:∀η ell:ℝ,0≤η→0≤ell→η≤capSmall→ell≤capSmall→
      τ+capSmall≤p^2/4 ∧ τ+capSmall+(p*ell+capSmall)≤ζfresh*κscale*p/4 ∧
      capSmall+η≤ζfresh*κscale*p/4 ∧ capSmall+η+4*p≤rate:=by
    intro η ell hη hell hηcap hellcap
    have hprod:0≤p*ell:=mul_nonneg hp.le hell
    have hprodle:p*ell≤ell:=by nlinarith [mul_nonneg (show 0≤1-p by linarith) hell]
    have hcombo:p*ell+capSmall≤cap:=by dsimp [capSmall] at *;linarith
    exact hRates τ capSmall η (p*ell+capSmall) hτ.le hc.le hη (by positivity)
      (hτcap.trans hcCap) hcCap (hηcap.trans hcCap) hcombo
  obtain ⟨eps,γgeo,heps,heps1,hγgeo,hgeo⟩:=hgeo (cLinear*τ) (by positivity)
  have hgeo':=ordinary_vortex_buffered_root_static_geometry_sampling_rate_mono 3 k 2 ρ₀ βparent b B εparent gap
    β ξ ζ edit pGeo p (cLinear*τ) eps γgeo hp.le hpSmall hgeo
  exact ⟨τ,hτeq,hτ,hτcap,hτ1,hnum,eps,γgeo,heps,heps1,hγgeo,hgeo',hcleanup⟩
end Oberwolfach
