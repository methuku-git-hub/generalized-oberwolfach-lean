module

public import Oberwolfach.OrdinaryTriangleRootFreeInnerRateGeometryAlignment
public import Oberwolfach.OrdinaryRootSharpPackingToleranceDecEq

@[expose] public section
/-! Fix the geometry's packing tolerance before the later conflict bound;
the certificate can use its own larger, conflict-dependent tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleRootFreeInnerFixedPacking
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ):Prop :=
    ∀(b₀:ℕ) (L:ℝ),0≤L→∃n₀ Nclean:ℕ,
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
      α ω βparent β b B h δref εparent εstar (cLinear*τ) ξ ζ p ε f binner c)→
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

theorem ordinary_triangle_root_free_inner_fixed_packing
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ)
    (h:OrdinaryTriangleRootFreeSharpInnerAfterCleanup α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
      p βe βh ν cap εsup δsample τ):
    OrdinaryTriangleRootFreeInnerFixedPacking α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
      p βe βh ν cap εsup δsample τ :=by
  intro b₀ L hL
  obtain ⟨ηpack,hη,hηbound,n₀,Nclean,hrest⟩:=h b₀ L hL
  refine ⟨n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,Ninner,Nsafe,hrest⟩:=hrest ε hε
  refine ⟨Nreserve,Ninner,Nsafe,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnsafe loss hloss hloss8 P Q F H π d X T Z W
    ηrate ellrate b₁ c₁ deep crossLoss D βparent hparent εparent ξ ζ f binner c
    pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold s j weight raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hW hQF hmE hmH hinner hX32 hV16 hJv hJu inputs hub hF hLfactor
    κscale hnum hbal hdiv rate cost deepCost hrate hcost hdeep
  obtain ⟨refdata⟩:=href
  have href':=ordinary_root_sharp_packing_tolerance_decEq P Q F H X T Z W 3 k (by decide)
    (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) b₁ c₁ deep crossLoss D
    α ω βparent β b B hparent δref εparent εstar (cLinear*τ) ηpack ξ ζ p ε f binner c hηbound refdata
  exact hrest V U Γ Color hn hnsafe loss hloss hloss8 P Q F H π d X T Z W
    ηrate ellrate b₁ c₁ deep crossLoss D βparent hparent εparent ξ ζ f binner c
    pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold s j weight raw
    hcut hTX hWZ hsize hreserve hlossbound ⟨href'⟩ hT hW hQF hmE hmH hinner hX32 hV16 hJv hJu inputs hub hF hLfactor
    κscale hnum hbal hdiv rate cost deepCost hrate hcost hdeep
end Oberwolfach
