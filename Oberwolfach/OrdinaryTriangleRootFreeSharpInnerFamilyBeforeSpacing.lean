module

public import Oberwolfach.OrdinaryTriangleRootFreeSharpInnerBeforeConflict

@[expose] public section
/-! Name the triangle inner-certificate continuation after the root and hub
parameters have been selected, with conflict size left for later. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleRootFreeSharpInnerAfterChoice
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ):Prop :=
    ∀(p βe βh ν cap εsup δsample:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh)
      (hν:0<ν) (hcap:0<cap) (hsup:0<εsup) (hδsample:0<δsample),
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe (βh/2) ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧
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
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→
    (W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)→Disjoint Q F→
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
      ηrate*Fintype.card (V⊕U)≤deepCost→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W 3 cost deepCost

theorem ordinary_triangle_root_free_sharp_inner_family_before_spacing (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δref:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δref→δref<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀κe pmin bHub BHub:ℝ,0<κe→0<pmin→pmin≤1→0<bHub→0≤BHub→
    ∃εf ηhub ηend ζfresh εrows:ℝ,0<εf ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζfresh ∧ 0<εrows ∧
      OrdinaryTriangleRootFreeSharpInnerAfterChoice α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows :=by
  obtain ⟨N,hcert⟩:=ordinary_triangle_root_free_sharp_inner_before_conflict α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δref hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hlinear,hcert⟩:=hcert k hk ω β b B hpack δref hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hlinear,?_⟩
  intro κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
  exact hcert κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
end Oberwolfach
