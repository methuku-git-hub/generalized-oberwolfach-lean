module

public import Oberwolfach.OrdinaryTriangleUniformInnerHubEvent
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance
public import Oberwolfach.OrdinaryTriangleTraceInnerParentConditions
public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceOrdered
public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent

@[expose] public section
/-! The same two-step balance and all-edit hub events provide the actual
inner parent, its scaled conditions and hub weights on one protected trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_trace_selected_inner_bundle_with_exact_balance
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D mv:ℕ) (β ε ρ₀:ℝ)
    (Q:Vortex U P D β ε mv) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (α pmin hmin εfactor ηend εrows δparent εcount t lam:ℝ)
    (hα:0<α) (hβα:β≤α/8) (hpmin:0<pmin)
    (num:OrdinaryTriangleInnerNumericParameters pmin (ρ₀/8) εfactor ηend εrows δparent εcount t lam)
    (hβbalance:β≤2*δparent*(ρ₀/8)*pmin)
    (ηprofile ζbalance cBoundary δbalance rate C:ℝ) (mBalance:ℕ)
    (hbalance:OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηprofile ζbalance cBoundary δbalance rate d 2 β C mBalance)
    (hζ:ζbalance≤lam*ε/4) (hMbalance:mBalance≤mv)
    (M:ℕ) (hM:32≤M) (hMε:4/ε≤(M:ℝ))
    (hMb:((2*(3*d):ℕ):ℝ)≤lam*M) (hterminal:(M:ℝ)≤ε*mv/2)
    (θhost pR pH εR εH tP βe βh:ℝ)
    (hθ:cycleThreshold 3≤θhost) (hθhalf:1/2≤θhost) (hdegree:(θhost+α)*Fintype.card V≤D)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:pmin≤pH) (hhmin:hmin≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH) (hεR0:0≤εR) (hεRδ:εR≤δbalance) (hεR:2*εR≤εcount)
    (hεH0:0≤εH) (hεHδ:εH≤δbalance) (hεH:2*εH≤εcount) (htP:tP≤t)
    (hβe0:0≤βe) (hβe:βe≤cBoundary*ε) (hβh0:0≤βh) (hβh:βh≤cBoundary*ε)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (hs:∀u,s u j=pH)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D mv β ε Q π hπ pR pH s j σ)
    (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (hK:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (cost deepCost:ℕ→ℝ) (i:ℕ) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (bHub BHub ηHub capHub:ℝ) (p εsup τ ν ηcost ell ζfresh:ℝ) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζfresh:0<ζfresh):
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let ρi:=markedVortexPermutation Q π hπ (i+1);let Ploc:=P.comap f;let Floc:=F.comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);let raw:=ordinaryRawRestrictPair f g σ;
    let density:=θhost+α-β/2;let L:ℝ:=2*((3*d:ℕ):ℝ);
    let Jwin:=Finset.Icc (i+2-2) i;let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    let γ:=min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4);
    let θmatch:=ζfresh*(γ/4)*ε;
    ζbalance≤capHub→
    OrdinaryTriangleUniformInnerHubEvent P D mv d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _=>θhost+α-β/2) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ→
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (∀j∈Jwin,0≤cost j ∧ cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+ell≤θmatch*p/4→ν+ηcost≤θmatch*p/4→p≤4*θmatch→
    20*Real.sqrt (2*p)≤θmatch/2→
    2≤θmatch*p*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))/4→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw ∧
    0≤Ledit ∧ Ledit≤(lam*ε/4)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)) ∧
    (EndpointPhysicalEditedConditions Ploc Gloc Floc Hloc I B Iᶜ ρi d j (ρ₀/8) pmin pR pH L Ledit δparent raw ∧
    OrdinaryTriangleRootFirstScaledConditions Gloc Hloc I B p εsup τ ν ηcost ell ((γ/4)*ε) ζfresh ∧
    I.Nonempty ∧ M≤I.card ∧
    Fintype.card {v:markedVortexVertexType Q (i+1) // v∉I}≤I.card^2 ∧
    Fintype.card {u:markedVortexHubType Q (i+1) // u∉B}≤I.card^2 ∧
    (∀v,Floc.degree v≤2*(3*d)) ∧ (∀v,(Floc.degree v:ℝ)≤L) ∧
    (εR*I.card)+4*Ledit≤εrows*I.card ∧ (εH*B.card)+3*Ledit≤εrows*B.card ∧
    L≤(I.card:ℝ)/24 ∧ L≤εfactor*I.card ∧
    δparent+(2*40+(1+2*40)/(2*(ρ₀/8)*pmin))*L/I.card+
      (tP+10*(40/((ρ₀/8)*pmin^5))*Ledit/I.card)≤ηend ∧
    (3/4:ℝ)≤density ∧
    (∀x∉I,∀v∈insert x I,(3/4:ℝ)*I.card≤((I∩Ploc.neighborFinset v).card:ℝ))) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηHub Gloc Floc Hloc I B) ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,3∣(Finset.univ.filter (fun v=>Hloc v u)).card):=by
  intro F R J S H S₀ H₀ X T Z W f g I B ρi Ploc Floc Gloc Hloc raw density L Jwin Ledit γ θmatch
    hζcap hfamily htrace hstate hbal hdiv hcost hεsup hsupport hclass hblock hpκ hsqrt horder
  obtain ⟨hwin0,_hwinI,_hwinB,profile,_hnear,_hmargin,hLinner,hLparent⟩:=
    hbalance V U Γ Color P JQ JH D mv hreg hn hD hρlo hρhi hMbalance Q π hπ s j σ
      pR pH θhost εR εH βe βh hpR hpR1 hhmin hθhalf hdegree hpEq hs hεR0 hεRδ hεH0 hεHδ
      hβe0 hβe hβh0 hβh K hJQ hJH hK hgood cost deepCost i hi A G Hs htrace hstate hcost
  have hE:0≤Ledit:=by dsimp [Ledit];positivity
  have hRate:0≤lam*ε/4:=by
    have hlam:=num.lambda_pos
    positivity
  have hnle:(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)≤
      Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)):=by
    exact_mod_cast Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hEdit:Ledit≤(lam*ε/4)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)):=by
    have h1:=mul_le_mul_of_nonneg_right hζ (show (0:ℝ)≤Fintype.card (markedVortexVertexType Q (i+1)) by positivity)
    have h2:=mul_le_mul_of_nonneg_left hnle hRate
    exact hLparent.trans (h1.trans h2)
  have hh:=ordinary_triangle_trace_inner_parent_conditions P JQ JH D mv β ε ρ₀ Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm
    π hπ d α pmin εfactor ηend εrows δparent εcount t lam hα hβα hpmin num hβbalance M hM hMε hMb hterminal
    θhost pR pH εR εH Ledit tP (lam*ε/4) βe βh hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεH hE le_rfl htP
    s j σ hgood K cost deepCost i hi A G Hs p εsup τ ν ηcost ell ζfresh hp hp1 hτ hζfresh
    htrace hstate profile hEdit hεsup hsupport hclass hblock hpκ hsqrt horder
  have hcap:Ledit≤capHub*I.card:=hLinner.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hsub:Gloc≤Ploc\Floc:=ordinary_vortex_trace_full_parent_host_subgraph
    P JQ JH D mv β ε Q π d j σ K cost deepCost i A G Hs htrace hstate
  have hlevel:=hfamily (i+1) hi
  have hHub:=hlevel Ledit hE hcap Gloc Hloc
    (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) (hsub.trans sdiff_le)
  refine ⟨profile,hE,hEdit,hh,?_,?_⟩
  · convert hHub using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · have hexact:=ordinary_vortex_trace_local_exact_balance P S₀ G H₀ Hs D mv β ε Q 3 i cost deepCost A
        htrace hstate hbal hdiv
    convert hexact using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
