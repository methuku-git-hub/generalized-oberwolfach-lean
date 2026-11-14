module

public import Oberwolfach.OrdinaryVortexGeneralCertificateInnerBounds
public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceOrdered
public import Oberwolfach.OrdinaryVortexTraceFullParentHost
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance

@[expose] public section
/-! At a later protected trace, the sampled balance and all-edit inner event
supply the general wheel certificate's profile, hub weights, exact balance,
size, endpoint-error and matching-scale inputs on the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_trace_selected_certificate_inputs
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (mWheel:ℕ) (P JQ:SimpleGraph V) (JH:V→U→Prop) (D mv:ℕ) (β ε ρ₀:ℝ)
    (Q:Vortex U P D β ε mv) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D≤1) (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (α pmin hmin ηprofile ζbalance cBoundary δbalance rate C:ℝ) (mBalance:ℕ)
    (hbalance:OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηprofile ζbalance cBoundary δbalance rate d 2 β C mBalance)
    (hMbalance:mBalance≤mv) (M:ℕ) (hM:4/ε≤(M:ℝ)) (hterminal:(M:ℝ)≤ε*mv/2)
    (θhost pR pH εR εH βe βh:ℝ)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hhmin:hmin≤pH) (hθhalf:1/2≤θhost)
    (hdegree:(θhost+α)*Fintype.card V≤D) (hpEq:pR=initialIndexDensity U D*pH)
    (hεR0:0≤εR) (hεRδ:εR≤δbalance) (hεH0:0≤εH) (hεHδ:εH≤δbalance)
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
    (bHub BHub ηHub capHub δend rateParent ζh ζe γ eParent cMatch:ℝ)
    (hδend:0≤δend) (hR:εR≤δend/4) (hH:εH≤δend/4)
    (hRate0:0≤rateParent) (hRate:rateParent≤δend*ε/8)
    (hζcap:ζbalance≤capHub) (hζrate:ζbalance≤rateParent)
    (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:γ≤eParent) (hβeEq:βe=eParent*ε) (hc:0<cMatch)
    (hcBound:cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2):
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let ρi:=markedVortexPermutation Q π hπ (i+1);let Ploc:=P.comap f;let Floc:=F.comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);let raw:=ordinaryRawRestrictPair f g σ;
    let density:=θhost+α-β/2;let Jwin:=Finset.Icc (i+2-2) i;
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    let n:ℝ:=Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1));
    let κh:=γ*(1/4:ℝ)*ε;let κinner:=(1/4:ℝ)*ε;let θmatch:=cMatch*ε;
    OrdinaryUniformInnerHubEvent mWheel P D mv d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _=>density) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ→
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (∀j∈Jwin,0≤cost j ∧ cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw ∧
    0≤Ledit ∧ Ledit≤rateParent*n ∧ Ledit≤capHub*I.card ∧
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel Ploc Floc I B ρi d pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh bHub BHub ηHub (fun u=>s (g u)) j raw ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub BHub ηHub Gloc Floc Hloc I B) ∧
    (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hloc v u)).card) ∧
    I.Nonempty ∧ M≤I.card ∧ (ρ₀/8)*(I.card:ℝ)≤B.card ∧ B.card≤I.card ∧
    Fintype.card {u:markedVortexHubType Q (i+1) // u∉B}≤I.card^2 ∧
    Fintype.card {v:markedVortexVertexType Q (i+1) // v∉I}≤(ordinaryPhysicalInnerDomain I B).card^2 ∧
    εR*I.card+Ledit≤δend*I.card ∧ εH*B.card+Ledit≤δend*I.card ∧
    0<κh ∧ 0<κinner ∧ 0<θmatch ∧ κh*n≤γ*I.card ∧
    κinner*n≤(ordinaryPhysicalInnerDomain I B).card ∧ θmatch≤ζh*κh ∧ θmatch≤ζe*κinner ∧
    γ*I.card≤βe*n :=by
  intro F R J S H S₀ H₀ X T Z W f g I B ρi Ploc Floc Gloc Hloc raw density Jwin Ledit n κh κinner θmatch
    hfamily htrace hstate hbal hdiv hcost
  obtain ⟨_hwin0,_hwinI,_hwinB,profile,_hnear,_hmargin,hLinner,hLparent⟩:=
    hbalance V U Γ Color P JQ JH D mv hreg hn hD hρlo hρhi hMbalance Q π hπ s j σ
      pR pH θhost εR εH βe βh hpR hpR1 hhmin hθhalf hdegree hpEq hs hεR0 hεRδ hεH0 hεHδ
      hβe0 hβe hβh0 hβh K hJQ hJH hK hgood cost deepCost i hi A G Hs htrace hstate hcost
  have hE:0≤Ledit:=by dsimp [Ledit];positivity
  have hcap:Ledit≤capHub*I.card:=hLinner.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hnle:(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)≤n:=by
    dsimp [n];exact_mod_cast Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hEdit:Ledit≤rateParent*n:=by
    have h1:=mul_le_mul_of_nonneg_right hζrate (show (0:ℝ)≤Fintype.card (markedVortexVertexType Q (i+1)) by positivity)
    exact hLparent.trans (h1.trans (mul_le_mul_of_nonneg_left hnle hRate0))
  have hevent:=hfamily (i+1) hi Ledit hE hcap
  have hsub:Gloc≤Ploc\Floc:=ordinary_vortex_trace_full_parent_host_subgraph
    P JQ JH D mv β ε Q π d j σ K cost deepCost i A G Hs htrace hstate
  have hHub:=hevent Gloc Hloc (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) (hsub.trans sdiff_le)
  have hexact:=ordinary_vortex_trace_local_exact_balance P S₀ G H₀ Hs D mv β ε Q (mWheel+1) i cost deepCost A
    htrace hstate hbal hdiv
  have hnum:=ordinary_vortex_general_certificate_inner_bounds Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm (i+1) hi
    M hM hterminal δend εR εH rateParent Ledit hδend hR hH hRate hEdit ζh ζe γ eParent cMatch hζh hζe hγ he hc hcBound
  rw [←hβeEq] at hnum
  refine ⟨profile,hE,hEdit,hcap,?_,?_,?_,?_,?_⟩
  · convert hevent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hHub using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hexact.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hexact.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hnum using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
