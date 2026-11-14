module

public import Oberwolfach.OrdinaryVortexTraceCapCostWitness
public import Oberwolfach.OrdinarySampleTraceAdaptiveHubWeights

@[expose] public section
/-! At a realized protected level, the same-sample adaptive event supplies
hub weights together with the cleanup profile and balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_trace_cap_witness_hub_at
    (ε ρ₀ α pmin hmin η ζ δ δcap rate:ℝ) (d mWheel:ℕ) (b Bweight ηHub:ℝ)
    (hwitness:OrdinaryVortexTraceCapCostWitness ε ρ₀ α pmin hmin η ζ δ δcap rate d):
∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∀C:ℝ,0≤C→∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δ→0≤βh→βh≤δ→
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
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel (P.comap f) (F.comap f) I B ρ d
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card)
      (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh b Bweight ηHub (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ)→
    (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card)≤ζ*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsOfLength mWheel b Bweight ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B) :=by
  intro β hβ hβ1 hβδ C hC
  obtain ⟨m₀,hm₀,hmain⟩:=hwitness β hβ hβ1 hβδ C hC
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ htrace hstate
    ν ηCover ρCover parent hν0 hν hη0 hηCover hρ0 hρCover hcostEq hevent
  obtain ⟨hcap,hprofile,hbalance⟩:=hmain V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs htrace hstate ν ηCover ρCover hν0 hν hη0 hηCover hρ0 hρCover hcostEq
  refine ⟨hcap,hprofile,hbalance,?_⟩
  have hh:=ordinary_sample_trace_adaptive_hub_weights P F JQ G JH Hs π d mWheel σ j K X T Z W cost deepCost (i+1) A
    _ _ f.toEmbedding g ρ I B pR pH (θ+α-β/2) (εR*I.card) (εH*B.card)
    (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh b Bweight ηHub (fun u=>s (g u))
    htrace hstate hevent (by
      convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
