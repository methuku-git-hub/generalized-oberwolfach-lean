module

public import Oberwolfach.OrdinaryTriangleNormalizeSharpWitnessWithRates
public import Oberwolfach.OrdinaryTriangleRootFreeInnerFixedPacking

@[expose] public section
/-! Apply the selected inner triangle certificate directly to a sharp cover
with its actual absolute budgets, normalizing those budgets only internally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_fixed_inner_actual_cover
    (α:ℝ) (k:ℕ) (hk:4≤k) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ)
    (hfixed:OrdinaryTriangleRootFreeInnerFixedPacking α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
      p βe βh ν cap εsup δsample τ):
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
    (∀ηrate ellrate:ℝ,0≤ηrate→ηrate≤ηCap→0≤ellrate→ellrate≤ellCap→
      βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U) ∧
      βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U) ∧
      OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν ηrate (p*ellrate+δsample) κscale ζfresh ∧
      ν+ηrate+4*p≤rate)→
    rate*Fintype.card (V⊕U)≤cost → cover≤deepCost→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W 3 cost deepCost :=by
  intro b₀ L hL
  obtain ⟨n₀,Nclean,hrest⟩:=hfixed b₀ L hL
  refine ⟨n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,Ninner,Nsafe,hrest⟩:=hrest ε hε
  refine ⟨Nreserve,Ninner,Nsafe,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hsafe loss hloss hloss8 P Q F H π d X T Z W
    ξroot aLoad lam ellCap ηCap b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c
    pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold s j weight raw
    cover ell hV hroot hξroot ha hlam hellCap hηCap hell hcover D href
    hpackcut hTX hWZ hsize hreserve hlossbound hT hW hQF hinner hX hV16 hJv hJu inputs hub hF hLfactor
    hbal hdiv κscale rate cost deepCost hnum hcost hdeep
  obtain ⟨ηrate,ellrate,hη,hηcap,hell0,hellcap,hcovereq,helleq,D',href'⟩:=
    ordinary_triangle_normalize_sharp_witness_with_rates P Q F H X T Z W k hk ξroot aLoad lam ellCap ηCap
      hV hroot hξroot ha hlam hellCap hηCap hell hcover b₁ c₁ deep crossLoss α ω βparent β b B h δref
      εparent εstar (cLinear*τ) ξ ζ p ε f binner c D href
  obtain ⟨hmE,hmH,hscaled,hrate⟩:=hnum ηrate ellrate hη hηcap hell0 hellcap
  exact hrest V U Γ Color hn hsafe loss hloss hloss8 P Q F H π d X T Z W
    ηrate ellrate b₁ c₁ deep crossLoss D' βparent h εparent ξ ζ f binner c
    pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold s j weight raw
    hpackcut hTX hWZ hsize hreserve hlossbound href' hT hW hQF hmE hmH hinner hX hV16 hJv hJu inputs hub hF hLfactor
    κscale hscaled hbal hdiv rate cost deepCost hrate hcost (by simpa only [←hcovereq] using hdeep)
end Oberwolfach
