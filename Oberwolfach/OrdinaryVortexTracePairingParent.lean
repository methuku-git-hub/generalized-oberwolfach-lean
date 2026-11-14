module

public import Oberwolfach.OrdinaryVortexTraceCapWitnessHubAt
public import Oberwolfach.OrdinaryVortexPairingGeometry
public import Oberwolfach.OrdinaryPairingParentFromProfile

@[expose] public section
/-! On an actual protected trace, the common row and hub-weight events and
    original vortex geometry construct the general fresh-pairing parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_trace_pairing_parent
    (ε ρ₀ α pmin η ζ δ δcap rate Kdom ηf εf γ κ a lam b Bweight:ℝ) (d mWheel:ℕ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hηf:0<ηf) (hεf:0<εf)
    (hγ:0≤γ) (hκ:0≤κ) (ha:0<a) (hlam:0<lam) (hδcap0:0≤δcap)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hζlam:ζ≤lam)
    (hRrate:a*(2*Kdom)+2*lam≤pmin/2) (hHrate:a*(2*Kdom)+2*lam≤pmin*(ρ₀/8))
    (herr:6*lam≤ηf*a)
    (hwitness:OrdinaryVortexTraceCapCostWitness ε ρ₀ α pmin pmin η ζ δ δcap rate d):
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∀C:ℝ,0≤C→∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→pmin≤pH→pH≤1→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→εR≤lam→0≤εH→εH≤δ→εH≤lam→
      0≤βe→βe≤δ→γ≤βe→κ≤βe→0≤βh→βh≤δ→
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
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    ∀ν ηCover ρCover:ℝ,
    let parent:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
    0≤ν→ν≤rate*parent→0≤ηCover→ηCover≤rate*parent→0≤ρCover→ρCover≤rate→
    cost i=ν+ηCover+(2*(ρCover*parent)+C)→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel (P.comap f) (F.comap f) I B ρ d
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card)
      (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh b Bweight ηf (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ)→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γ κ b Bweight pmin a εf ηf
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I)
        (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q (i+1)↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr) (fun _=>pH)) :=by
  intro β hβ hβ1 hβδ C hC
  obtain ⟨v₀,hv₀,hmain⟩:=ordinary_vortex_trace_cap_witness_hub_at ε ρ₀ α pmin pmin η ζ δ δcap rate d mWheel b Bweight ηf hwitness β hβ hβ1 hβδ C hC
  obtain ⟨v₁,hv₁,hgeom⟩:=ordinary_vortex_pairing_geometry β ε ρ₀ Kdom εf d hβ hβ1 hε hε1 hρ₀ hεf hKdom
  refine ⟨max v₀ v₁,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hpH1 hθ hdegree hpEq hs hεR0 hεR hεRlam hεH0 hεH hεHlam hβe0 hβe hγβ hκβ hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ htrace hstate ν ηCover ρCover parent hν0 hν hη0 hηCover hρ0 hρCover hcostEq hevent
  obtain ⟨hcap,hprofile,hbalance,hHub⟩:=hmain V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi (by omega) Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs htrace hstate ν ηCover ρCover hν0 hν hη0 hηCover hρ0 hρCover hcostEq hevent
  have hg:=hgeom V U P D m hreg hn hD hρlo hρhi (by omega) Q π hπ (i+1) hi
  obtain ⟨hI,hsize,hZ,hBI,hF,hFsmall⟩:=hg
  let L:ℝ:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card
  have hL0:0≤L:=by dsimp [L];positivity
  have hL:L≤lam*I.card:=hcap.trans (mul_le_mul_of_nonneg_right hζlam (by positivity))
  have hR:εR*I.card≤lam*I.card:=mul_le_mul_of_nonneg_right hεRlam (by positivity)
  have hH:εH*B.card≤lam*I.card:=by
    have hh:=mul_le_mul_of_nonneg_left (show (B.card:ℝ)≤I.card by exact_mod_cast hBI) hεH0
    have hh':=mul_le_mul_of_nonneg_right hεHlam (show (0:ℝ)≤I.card by positivity)
    linarith only [hh,hh']
  refine ⟨hprofile,?_⟩
  exact ordinary_pairing_parent_from_profile mWheel (2*(3*d)) (P.comap f) (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) I B ρ d j (fun u=>s (g u)) γ κ b Bweight pmin a εf ηf pR pH
    (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (ρ₀/8) (2*Kdom) lam (ordinaryRawRestrictPair f g σ)
    hprofile hI hpmin (by positivity) hηf ha hlam hRrate hHrate herr hsize hZ hpR hpH hpH1
    (by positivity) hR (by positivity) hH hL0 hL hγ hκ hγβ hκβ hF hFsmall hHub
end Oberwolfach
