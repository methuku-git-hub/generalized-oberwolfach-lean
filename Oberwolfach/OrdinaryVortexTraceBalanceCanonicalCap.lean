module

public import Oberwolfach.OrdinaryVortexTraceBalanceUniformChosenMargins
public import Oberwolfach.OrdinaryVortexCleanupCanonicalCap
public import Oberwolfach.OrdinaryCleanupProfileEnlargeEdit

@[expose] public section
/-! The realized protected trace can use a deterministic pre-sampling edit
cap, with the cleanup margins and balance retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_trace_balance_with_canonical_cap
    (ε ρ₀ α pmin hmin η ζ:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin) (hη:0<η) (hζ:0<ζ):
    ∃δ δcap:ℝ,0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
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
    ordinaryHostResources G Hs=A→0≤cost i→cost i≤δ*I.card→cost i≤δ*B.card→
    (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card)≤ζ*I.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card):=by
  obtain ⟨δbal,hδbal,hδbalα,hbalance⟩:=ordinary_vortex_trace_balance_uniform_chosen_margins ε ρ₀ α pmin hmin η d
    hε hε1 hρ₀ hα hpmin hhmin hη
  obtain ⟨δcap,hδcap,hδcapα,hδcapζ,hcap⟩:=ordinary_vortex_cleanup_canonical_cap ε ρ₀ α pmin hmin η ζ d
    hε hε1 hρ₀ hα hpmin hhmin hη hζ
  let δ:=min δbal δcap
  have hδ:0<δ:=lt_min hδbal hδcap
  have hδbal':δ≤δbal:=min_le_left _ _
  have hδcap':δ≤δcap:=min_le_right _ _
  refine ⟨δ,δcap,hδ,hδbal'.trans hδbalα,hδcap,hδcapζ,?_⟩
  intro β hβ hβ1 hβδ
  obtain ⟨mb,hmb,hb⟩:=hbalance β hβ hβ1 (hβδ.trans hδbal')
  obtain ⟨mc,hmc,hc⟩:=hcap β hβ hβ1 (hβδ.trans hδcap')
  refine ⟨max mb mc,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ htrace hstate hcost0 hcostI hcostB
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hB0:(0:ℝ)≤B.card:=by positivity
  have hcostIbal:cost i≤δbal*I.card:=hcostI.trans (mul_le_mul_of_nonneg_right hδbal' hI0)
  have hcostBbal:cost i≤δbal*B.card:=hcostB.trans (mul_le_mul_of_nonneg_right hδbal' hB0)
  obtain ⟨hprofile,hbalance⟩:=hb V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi (by omega) Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 (hεR.trans hδbal') hεH0 (hεH.trans hδbal')
    hβe0 (hβe.trans hδbal') hβh0 (hβh.trans hδbal') K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs htrace hstate hcost0 hcostIbal hcostBbal
  have hnum:=hc V U P D m hreg hn hD hρlo hρhi (by omega) Q (i+1) hi pR pH θ εR εH βe βh
    hpRlo hpR1 hpHlo hθ hεR0 (hεR.trans hδcap') hεH0 (hεH.trans hδcap')
    hβe0 (hβe.trans hδcap') hβh0 (hβh.trans hδcap')
  have hcostCap:cost i≤δcap*min (I.card:ℝ) B.card:=by
    rcases le_total (I.card:ℝ) B.card with hh | hh
    · rw [min_eq_left hh]
      exact hcostI.trans (mul_le_mul_of_nonneg_right hδcap' hI0)
    · rw [min_eq_right hh]
      exact hcostB.trans (mul_le_mul_of_nonneg_right hδcap' hB0)
  have hLL:2*((3*d:ℕ):ℝ)+cost i≤2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card:=by linarith
  refine ⟨hnum.2.2.2.2.1,?_,hbalance⟩
  exact ordinary_cleanup_profile_enlarge_edit (P.comap f) (G.comap f) (F.comap f)
    (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2) (εR*I.card) (εH*B.card)
    (2*((3*d:ℕ):ℝ)+cost i) (2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card) βe βh
    (fun u=>s (g u)) j (ordinaryRawRestrictPair f g σ) hprofile hLL hnum.2.2.2.2.2.1 hnum.2.2.2.2.2.2.1
end Oberwolfach
