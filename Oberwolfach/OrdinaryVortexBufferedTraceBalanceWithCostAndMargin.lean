module

public import Oberwolfach.OrdinaryVortexBufferedTraceBalanceWithExplicitMargin
public import Oberwolfach.OrdinaryVortexBufferedCostGeometry
public import Oberwolfach.OrdinaryVortexProtectedBufferedTraceLocalBalance
public import Oberwolfach.OrdinaryVortexCleanupUniformOriginalMargins

@[expose] public section
/-! Choose cleanup tolerances before the vortex and obtain the profile and
balance on each actual protected trace, with the numerical margins supplied
by the vortex geometry and the latest-loss bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_buffered_trace_balance_with_cost_and_margin
    (ε ρ₀ α pmin hmin η:ℝ) (d buffer:ℕ) (hbuffer:2≤buffer) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin) (hη:0<η):
    ∃δ rate:ℝ,0<δ ∧ δ≤α ∧ 0<rate ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
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
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    let Jwin:=Finset.Icc (i+2-buffer) i;
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→
    (∀j∈Jwin,0≤cost j ∧ cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
    0≤(∑j∈Jwin,cost j) ∧ (∑j∈Jwin,cost j)≤δ*I.card ∧ (∑j∈Jwin,cost j)≤δ*B.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j)) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+
      3*(2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j))≤η*I.card:=by
  obtain ⟨δ,hδ,hδα,hbalance⟩:=ordinary_vortex_buffered_trace_balance_with_explicit_margin ε ρ₀ α pmin hmin η d
    hε hε1 hρ₀ hα hpmin hhmin hη
  obtain ⟨rate,hrate,hcostgeo⟩:=ordinary_vortex_buffered_cost_from_geometry ε ρ₀ δ buffer hbuffer hε hε1 hρ₀ hδ
  refine ⟨δ,rate,hδ,hδα,hrate,?_⟩
  intro β hβ hβ1 hβδ C hC
  obtain ⟨mb,hmb,hbalance⟩:=hbalance β hβ hβ1 hβδ
  obtain ⟨mc,hmc,hcostgeo⟩:=hcostgeo β hβ hβ1 C hC
  refine ⟨max mb mc,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ Jwin htrace hstate hcost
  have hwin:=hcostgeo V U P D m hreg hn hD hρlo hρhi (by omega) Q i hi cost hcost
  obtain ⟨hprofile,hnear,hmargin⟩:=hbalance V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi (by omega) Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i buffer hbuffer hi A G Hs htrace hstate hwin.1 hwin.2.1 hwin.2.2
  exact ⟨hwin.1,hwin.2.1,hwin.2.2,hprofile,hnear,hmargin⟩
end Oberwolfach
