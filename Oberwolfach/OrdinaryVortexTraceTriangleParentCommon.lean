module

public import Oberwolfach.OrdinaryVortexTraceCapWitnessHubAt
public import Oberwolfach.OrdinaryFixedVortexDeepParentMargins
public import Oberwolfach.OrdinaryTriangleParentFromCommonLengthWeights
public import Oberwolfach.OrdinaryProtectedTraceHostLe

@[expose] public section
/-! On a protected later-level trace, use the common row, hub and endpoint
samples to build the triangle fresh-factor parent for the actual remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_trace_triangle_parent_from_common
    (ε ρ₀ α pmin η ζ δ δcap rate Kdom ηHub εf γ κ δparent εparent tpot lam b Bweight:ℝ) (d:ℕ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hζlam:ζ≤lam) (hδcap0:0≤δcap)
    (hwitness:OrdinaryVortexTraceCapCostWitness ε ρ₀ α pmin pmin η ζ δ δcap rate d)
    (num:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηHub εf (2*Kdom)
      γ κ δparent εparent tpot lam b Bweight):
∀β:ℝ,0≤β→β≤1/4→β≤δ→β≤α/8→β≤2*δparent*(ρ₀/8)*pmin→
    ∀C:ℝ,0≤C→∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→pmin≤pH→pH≤1→1/2≤θ→cycleThreshold 3≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→2*εR≤εparent→0≤εH→εH≤δ→2*εH≤εparent→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(K:Finset (Sym2 V⊕(V×U))),
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D m β ε Q π hπ pR pH s j σ→
    ∀(cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop),
    let F:=permutationConflictGraph π (3*d);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→
    ∀ν ηCover ρCover:ℝ,
    let parent:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    0≤ν→ν≤rate*parent→0≤ηCover→ηCover≤rate*parent→0≤ρCover→ρCover≤rate→
    cost i=ν+ηCover+(2*(ρCover*parent)+C)→
    OrdinaryAdaptiveHubWeightsLevelEvent 2 (P.comap f) (F.comap f) I B ρ d
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card)
      (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh b Bweight ηHub (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ)→
    ∀(weight:markedVortexVertexType Q (i+1)→Sym2 (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→ℝ),
    EndpointPhysicalParentWeights (P.comap f) I Iᶜ weight→
    EndpointPhysicalPotentialEvent (P.comap f) (F.comap f) I B Iᶜ ρ d j weight pR pH tpot
      (ordinaryRawRestrictPair f g σ)→
    (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card)≤ζ*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsOfLength 2 b Bweight ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B) ∧
    Nonempty (MixedFreshParentDataInsideRoots γ κ b Bweight εf ηHub
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I)
        (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q (i+1)↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr)) := by
  intro β hβ hβ1 hβδ hβα hβbal C hC
  obtain ⟨v₀,hv₀,hmain⟩:=ordinary_vortex_trace_cap_witness_hub_at ε ρ₀ α pmin pmin η ζ δ δcap rate d 2 b Bweight ηHub hwitness β hβ hβ1 hβδ C hC
  obtain ⟨v₁,hv₁,hmargin⟩:=ordinary_fixed_vortex_deep_parent_margins β ε ρ₀ α pmin Kdom ηHub εf γ κ δparent εparent tpot lam b Bweight
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom num hβbal d
  refine ⟨max v₀ v₁,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hpH1 hθ hthreshold hdegree hpEq hs hεR0 hεR hεRp hεH0 hεH hεHp hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ htrace hstate
    ν ηCover ρCover parent hν0 hν hη0 hηCover hρ0 hρCover hcostEq hevent weight hparent hepoint
  obtain ⟨hcap,hprofile,hbalance,hHub⟩:=hmain V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi (by omega) Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs htrace hstate ν ηCover ρCover hν0 hν hη0 hηCover hρ0 hρCover hcostEq hevent
  refine ⟨hcap,hprofile,hbalance,hHub,?_⟩
  let L:ℝ:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card
  have hL0:0≤L:=by
    dsimp [L]
    positivity
  have hL:L≤lam*I.card:=hcap.trans (mul_le_mul_of_nonneg_right hζlam (by positivity))
  have margins:=hmargin V U P D m hreg hn hD hρlo hρhi (by omega) Q π hπ θ pR pH εR εH L
    hthreshold hdegree hpR hpR1 hpH hpH1 hpEq hεR0 hεRp hεH0 hεHp hL0 (i+1) hi hL
  have hQ0:S₀≤P\F:=by
    intro v w hvw
    exact ⟨(retainedGraph_le P _) hvw.1.1.1,hvw.1.1.2⟩
  have hG0:=ordinary_protected_trace_host_le S₀ G H₀ Hs X T Z W cost deepCost (i+1) A htrace hstate
  have hQ:(G.comap f)≤(P.comap f)\(F.comap f):=by
    intro v w hvw
    exact hQ0 (hG0 hvw)
  have hrows:= (hgood (i+1) hi).1
  obtain ⟨hweight⟩:=hHub
  have hout:=ordinary_triangle_parent_from_common_length_weights (P.comap f) (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) I B ρ d j (fun u=>s (g u)) weight γ κ b Bweight εf ηHub (ρ₀/8) pmin pR pH
    (θ+α-β/2) (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)) L βe βh δparent εparent tpot (2*Kdom) (pR*β*I.card)
    (ordinaryRawRestrictPair f g σ) margins hQ hprofile hrows hparent hepoint hweight
  exact ⟨hout⟩
end Oberwolfach
