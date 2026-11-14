module

public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt

@[expose] public section
/-! A fixed-parameter initial balance selector may be appended to any
common event, uniformly over protections chosen after sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_initial_ambient_balance_at_adaptive_probability
    (ε ρ₀ α pmin hmin η cBoundary δ:ℝ) (d:ℕ) (β:ℝ) (m₀:ℕ)
    (hAt:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin η cBoundary δ d β m₀):
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U] (P:SimpleGraph V) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (pR pH θ εR εH βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
      , pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (outcome:Ω→RawWheelOutcome V U Γ Color)
      (E:Ω→Prop) (bound:ℝ), bound≤μ.probability E→
      (∀z,E z→OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D m β ε Q π hπ pR pH s j (outcome z))→
    bound≤μ.probability (fun z=>E z ∧ (∀(JQ:SimpleGraph V) (JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U))),
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈Q.extendedVertices 1∧u∈Q.extendedIndices 1))→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
    let S:=(rawWheelGraph P (outcome z)\permutationConflictGraph π (3*d))\JQ;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>rawWheelSpokes π d (outcome z) j v u∧¬JH v u∧¬(Sum.inr (v,u)∈K);
    ∀i:ℕ,i+1<Q.length→
    let I:=markedVortexInnerVertices Q (i+1);
    (∀v∈Q.extendedVertices (i+2),|((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤η*I.card) ∧
    (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤η*I.card))) :=by
  intro V U Γ Color _ _ _ _ _ _ P D m hreg hn hD hρlo hρhi hmm Q π hπ
    pR pH θ εR εH βe βh s j hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs Ω _ μ outcome E bound hprob hrow
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz,?_⟩
  intro JQ JH K hJQ hJH havoid
  exact hAt V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hmm Q π hπ
    pR pH θ εR εH βe βh s j (outcome z) K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs hJQ hJH havoid (hrow z hz)
end Oberwolfach
