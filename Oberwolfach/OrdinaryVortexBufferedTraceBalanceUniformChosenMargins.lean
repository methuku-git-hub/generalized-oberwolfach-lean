module

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

theorem ordinary_vortex_buffered_trace_balance_uniform_chosen_margins
    (ε ρ₀ α pmin hmin η:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin) (hη:0<η):
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→
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
    ∀(cost deepCost:ℕ→ℝ) (i buffer:ℕ),2≤buffer→i+1<Q.length→
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
    ordinaryHostResources G Hs=A→0≤(∑j∈Jwin,cost j)→(∑j∈Jwin,cost j)≤δ*I.card→(∑j∈Jwin,cost j)≤δ*B.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j)) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card):=by
  obtain ⟨δ,hδ,hδα,hmain⟩:=ordinary_vortex_cleanup_uniform_original_margins ε ρ₀ α pmin hmin η (3*d)
    hε hε1 hρ₀ hα hpmin hhmin hη
  refine ⟨δ,hδ,hδα,?_⟩
  intro β hβ0 hβ1 hβ
  obtain ⟨m₀,hm₀,hmargin⟩:=hmain β hβ0 hβ1 hβ
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpRlo hpR1 hpHlo hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh K hJQ hJH havoid hgood
    cost deepCost i buffer hbuffer hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ Jwin htrace hstate hcost hcostI hcostB
  have hρ:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
  have hpR:0<pR:=lt_of_lt_of_le hpmin hpRlo
  have hpH:0<pH:=lt_of_lt_of_le hhmin hpHlo
  have hdensity:1/2≤θ+α-β/2:=by linarith
  have hnum:=hmargin V U P D m hreg hn hD hρlo hρhi hm Q (i+1) hi
    pR pH θ εR εH βe βh ((∑j∈Jwin,cost j)) hpRlo hpR1 hpHlo hθ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hcost hcostI hcostB
  have hbal:=hnum.2.2
  rw [hpEq] at hbal
  exact ordinary_vortex_protected_buffered_trace_local_balance P JQ JH D m β ε θ α pR pH εR εH Q π hπ d s j σ
    hn hreg hρ hβ0 hpR.le hpR1 hpH.le hεR0 hεH0 hdensity hdegree hpEq hs K hJQ hJH havoid hgood
    cost deepCost i buffer hbuffer hi A G Hs βe βh η htrace hstate hcost hnum.1 hnum.2.1 hbal
end Oberwolfach
