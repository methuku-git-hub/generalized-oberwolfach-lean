module

public import Oberwolfach.OrdinaryTriangleRootFreeFixedActualCoverCapped
public import Oberwolfach.OrdinaryTriangleRootFreeCoherentEarlyChoices

@[expose] public section
/-! The shared rate selection directly supplies the actual-cover callback,
including its separate deeper budget, after the conflict bound is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleRootFreeActualCoverAfterCleanup
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ):Prop :=
    ∀(b₀:ℕ) (L:ℝ),0≤L→∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Ninner Nsafe:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nsafe≤Fintype.card (V⊕U)→
    ∀(loss:ℝ),0≤loss→loss≤1/8→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U)
      (ξroot aLoad lam ellCap ηCap b₁ c₁ deep crossLoss:ℝ)
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold:ℝ)
      (s:U→Color→ℝ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ) (raw:RawWheelOutcome V U Γ Color),
    let cover:=10*ξroot*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card V*3+(T.card:ℝ)*3);
    0<Fintype.card V→(T.card:ℝ)+W.card≤lam*Fintype.card V→
    0≤ξroot→0≤aLoad→0≤lam→0≤ellCap→0≤ηCap→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap→10*ξroot≤ηCap→
    ∀(D:OrdinaryRootCoverNonrootData Q F H X T Z W 3 cover ell),
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss D α ω βparent β b B h δref εparent εstar (cLinear*τ) ξ ζ p ε f binner c)→
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^1≤loss→
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→
    (W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)→Disjoint Q F→
    Ninner≤X.card→32≤X.card→16≤Fintype.card V→
    Fintype.card {v:V // v∉X}≤X.card^2→Fintype.card {u:U // u∉Z}≤X.card^2→
    OrdinaryDeepParentIngredients P Q F H X Z π d j s weight γold κold bold Bold εold ηend κe pmin
      pR pH density tR tH L Ledit βe₀ βh₀ δbal εrows tP K raw→
    OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub Q F H X Z→
    (∀v,F.degree v≤b₀)→L≤εf*X.card→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀κscale rate cost deepCost:ℝ,
    OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν ηCap (p*ellCap+δsample) κscale ζfresh→
    βe+3*max ηCap ellCap≤βe₀→βh+2*ellCap≤βh₀→ν+ηCap+4*p≤rate→
    rate*Fintype.card (V⊕U)≤cost → cover≤deepCost→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W 3 cost deepCost

theorem ordinary_triangle_root_free_rate_actual_cover
    (α:ℝ) (k:ℕ) (hk:4≤k) (ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (ρ₀ βparent εparent gap ξreserve ζ edit eParent hParent γbase ε βe βh ellCap:ℝ)
    (hafter:OrdinaryTriangleRootFreeRateAfterVortex α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub
      εf ηhub ηend ζfresh εrows ρ₀ βparent εparent gap ξreserve ζ edit eParent hParent γbase ε βe βh ellCap):
    ∀rate pcap othercap:ℝ,0<rate→0<pcap→0<othercap→
    ∃p εsup capSmall δsample ν:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζfresh*(γbase*ε) ∧
      20*Real.sqrt (2*p)≤ζfresh*(γbase*ε)/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<capSmall ∧ capSmall≤othercap ∧ capSmall≤ellCap ∧
      0<δsample ∧ 0<ν ∧ ν≤capSmall ∧
    ∃Norder:ℕ,(∀n:ℕ,Norder≤n→2≤ζfresh*(γbase*ε)*p*n/4) ∧
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe (βh/2) ν (min capSmall 1) ∧
      0<τ ∧ τ≤capSmall ∧ τ≤1 ∧
      τ+ν≤p^2/4 ∧ τ+ν+(p*ellCap+δsample)≤ζfresh*(γbase*ε)*p/4 ∧
      ν+capSmall≤ζfresh*(γbase*ε)*p/4 ∧ ν+capSmall+4*p≤rate ∧
      βe+3*max capSmall ellCap≤eParent*ε ∧ βh+2*ellCap≤hParent*ε ∧
    ∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap
        βout ξreserve ζ edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ
 :=by
  intro rate pcap othercap hrate hpcap hother
  obtain ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpκ,hsqrt,hεsup,hεsupCap,hcap,hcapother,hcapell,
    hδ,hν,hνcap,Norder,horder,τ,hτeq,hτ,hτcap,hτ1,hsupport,hclass,hblock,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,heps,heps1,hγgeo,hgeometry,hfixed⟩:=hafter rate pcap othercap hrate hpcap hother
  refine ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpκ,hsqrt,hεsup,hεsupCap,hcap,hcapother,hcapell,
    hδ,hν,hνcap,Norder,horder,τ,hτeq,hτ,hτcap,hτ1,hsupport,hclass,hblock,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,heps,heps1,hγgeo,hgeometry,?_⟩
  exact ordinary_triangle_root_free_fixed_inner_actual_cover_capped α k hk ω βout b B hpack δref εstar cLinear κe pmin bHub BHub
    εf ηhub ηend ζfresh εrows p βe βh ν capSmall εsup δsample τ hfixed
end Oberwolfach
