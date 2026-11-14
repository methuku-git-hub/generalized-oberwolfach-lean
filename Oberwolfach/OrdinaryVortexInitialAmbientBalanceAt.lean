module

public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceUniform

@[expose] public section
/-! A reusable fixed-parameter form of the initial balance selector, with
monotonicity in its boundary, error, and host-size thresholds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexInitialAmbientBalanceAt
    (ε ρ₀ α pmin hmin η cBoundary δ:ℝ) (d:ℕ) (β:ℝ) (m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U] (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (pR pH θ εR εH βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
      (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U))),
      pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈Q.extendedVertices 1∧u∈Q.extendedIndices 1))→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ→
    let S:=(rawWheelGraph P σ\permutationConflictGraph π (3*d))\JQ;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>rawWheelSpokes π d σ j v u∧¬JH v u∧¬(Sum.inr (v,u)∈K);
    ∀i:ℕ,i+1<Q.length→
    let I:=markedVortexInnerVertices Q (i+1);
    (∀v∈Q.extendedVertices (i+2),|((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤η*I.card) ∧
    (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤η*I.card)

theorem ordinary_vortex_initial_ambient_balance_at_monotone
    (ε ρ₀ α pmin hmin η cSmall cLarge δSmall δLarge:ℝ) (d:ℕ) (β:ℝ) (mSmall mLarge:ℕ)
    (hε:0≤ε) (hc:cSmall≤cLarge) (hδ:δSmall≤δLarge) (hm:mSmall≤mLarge)
    (hbig:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin η cLarge δLarge d β mSmall):
    OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin η cSmall δSmall d β mLarge :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hmm Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs hJQ hJH havoid hgood
  have hbe:βe≤cLarge*ε:=hβec.trans (mul_le_mul_of_nonneg_right hc hε)
  have hbh:βh≤cLarge*ε:=hβhc.trans (mul_le_mul_of_nonneg_right hc hε)
  exact hbig V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi (by omega) Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR (hεRδ.trans hδ) hεH (hεHδ.trans hδ)
    hβe hbe hβh hbh hpEq hs hJQ hJH havoid hgood

theorem ordinary_vortex_initial_ambient_balance_at_choice
    (ρ₀ α pmin hmin:ℝ) (d:ℕ) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃c:ℝ,0<c ∧ ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ δ≤η ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin η c δ d β m₀ :=by
  exact ordinary_vortex_initial_ambient_balance_uniform ρ₀ α pmin hmin d hρ₀ hα hpmin hhmin
end Oberwolfach
