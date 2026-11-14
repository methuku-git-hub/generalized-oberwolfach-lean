module

public import Oberwolfach.OrdinaryTriangleUniformInnerHubEvent
public import Oberwolfach.OrdinaryVortexInitialLocalExactBalance
public import Oberwolfach.OrdinaryTriangleInitialInnerParentConditions
public import Oberwolfach.OrdinaryTriangleInitialCorrectedParentBridge
public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent

@[expose] public section
/-! The actual corrected initial host, the sampled row event and the
all-edit hub event yield the inner parent and hub weights together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_initial_selected_inner_bundle_with_exact_balance
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ) (β ε ρ₀:ℝ)
    (Q:Vortex U P D β ε mv) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (hi:0<Q.length)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (α pmin εfactor ηend εrows δ εcount t lam:ℝ)
    (hα:0<α) (hβα:β≤α/8) (hpmin:0<pmin)
    (num:OrdinaryTriangleInnerNumericParameters pmin (ρ₀/8) εfactor ηend εrows δ εcount t lam)
    (hβbalance:β≤2*δ*(ρ₀/8)*pmin)
    (M:ℕ) (hM:32≤M) (hMε:4/ε≤(M:ℝ))
    (hMb:((2*(3*d):ℕ):ℝ)≤lam*M) (hterminal:(M:ℝ)≤ε*mv/2)
    (θhost pR pH εR εH Ledit tP ζedit βe βh:ℝ)
    (hθ:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*Fintype.card V≤D)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:pmin≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH) (hεR:2*εR≤εcount) (hεH:2*εH≤εcount)
    (hE:0≤Ledit) (hζedit:0≤ζedit) (hζrate:ζedit≤lam*ε/4) (htP:tP≤t)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D mv β ε Q π hπ pR pH s j σ)
    (bHub BHub ηHub capHub:ℝ) (p εsup τ ν η ell ζfresh:ℝ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζfresh:0<ζfresh):
    let F:=permutationConflictGraph π (3*d);let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let Ploc:=P.comap f;let Floc:=F.comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let raw:=ordinaryRawRestrictPair f g σ;let density:=θhost+α-β/2;let L:ℝ:=2*((3*d:ℕ):ℝ);
    let γ:=min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4);let θmatch:=ζfresh*(γ/4)*ε;
    ζedit≤capHub→
    OrdinaryTriangleUniformInnerHubEvent P D mv d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _=>θhost+α-β/2) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ→
    G≤P→Disjoint G F→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→Ledit≤ζedit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw→
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+ell≤θmatch*p/4→ν+η≤θmatch*p/4→p≤4*θmatch→
    20*Real.sqrt (2*p)≤θmatch/2→
    2≤θmatch*p*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)/4→
    (EndpointPhysicalEditedConditions Ploc Gloc Floc Hloc I B Iᶜ ρi d j (ρ₀/8) pmin pR pH L Ledit δ raw ∧
    OrdinaryTriangleRootFirstScaledConditions Gloc Hloc I B p εsup τ ν η ell ((γ/4)*ε) ζfresh ∧
    I.Nonempty ∧ M≤I.card ∧
    Fintype.card {v:markedVortexVertexType Q 0 // v∉I}≤I.card^2 ∧
    Fintype.card {u:markedVortexHubType Q 0 // u∉B}≤I.card^2 ∧
    (∀v,Floc.degree v≤2*(3*d)) ∧ (∀v,(Floc.degree v:ℝ)≤L) ∧
    (εR*I.card)+4*Ledit≤εrows*I.card ∧ (εH*B.card)+3*Ledit≤εrows*B.card ∧
    L≤(I.card:ℝ)/24 ∧ L≤εfactor*I.card ∧
    δ+(2*40+(1+2*40)/(2*(ρ₀/8)*pmin))*L/I.card+
      (tP+10*(40/((ρ₀/8)*pmin^5))*Ledit/I.card)≤ηend ∧
    (3/4:ℝ)≤density ∧
    (∀x∉I,∀v∈insert x I,(3/4:ℝ)*I.card≤((I∩Ploc.neighborFinset v).card:ℝ))) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηHub Gloc Floc Hloc I B) ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,3∣(Finset.univ.filter (fun v=>Hloc v u)).card):=by
  intro F f g I B ρi Ploc Floc Gloc Hloc raw density L γ θmatch hζcap hfamily hG hGF hbal hdiv hLedit profile
    hεsup hsupport hclass hblock hpκ hsqrt horder
  obtain ⟨hQ,hEdit⟩:=ordinary_triangle_initial_corrected_parent_bridge Q G F hG hGF Ledit ζedit (lam*ε/4)
    hζedit hζrate hLedit
  have hh:=ordinary_triangle_initial_inner_parent_conditions P D mv β ε ρ₀ Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm hi
    π hπ d α pmin εfactor ηend εrows δ εcount t lam hα hβα hpmin num hβbalance M hM hMε hMb hterminal
    θhost pR pH εR εH Ledit tP (lam*ε/4) βe βh hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεH hE le_rfl htP
    s j σ hgood Gloc Hloc p εsup τ ν η ell ζfresh hp hp1 hτ hζfresh
    profile hQ hEdit hεsup hsupport hclass hblock hpκ hsqrt horder
  have hcap:Ledit≤capHub*I.card:=hLedit.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hsub:Gloc≤Ploc:=by intro v w hvw;exact hG hvw
  have hlevel:=hfamily 0 hi
  have hHub:=hlevel Ledit hE hcap Gloc Hloc
    (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hsub
  refine ⟨hh,?_,?_⟩
  · convert hHub using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · have hexact:=ordinary_vortex_initial_local_exact_balance P G Hs D mv β ε Q 3 hbal hdiv
    convert hexact using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
