module

public import Oberwolfach.OrdinaryVortexInnerHistoryBudgetFromMargins
public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt

@[expose] public section
/-! Assemble both initial ambient balance inputs and the recent inner
history budget on the same protected sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_history_inputs_from_margins
    (ε ρ₀ α pmin hmin ηinitial cBoundary δ:ℝ) (d:ℕ) (β:ℝ) (m₀:ℕ)
    (hAt:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηinitial cBoundary δ d β m₀)
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1) (hm:m₀≤m)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (pR pH θ εR εH βe βh:ℝ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U)))
    (hpmin:0≤pmin) (hβ:0≤β) (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:hmin≤pH) (hθ:1/2≤θ)
    (hdegree:(θ+α)*Fintype.card V≤D) (hεR:0≤εR) (hεRδ:εR≤δ) (hεH:0≤εH) (hεHδ:εH≤δ)
    (hβe:0≤βe) (hβec:βe≤cBoundary*ε) (hβh:0≤βh) (hβhc:βh≤cBoundary*ε)
    (hpEq:pR=initialIndexDensity U D*pH) (hs:∀u,s u j=pH)
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1∧u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (i buffer:ℕ) (hi:i+1<Q.length) (cost:ℕ→ℝ) (ηprofile ηtarget:ℝ)
    (hcost:∀t∈Finset.Icc (i+2-buffer) i,0≤cost t)
    (hinit:ηinitial≤ηtarget/2) (hprofile:ηprofile≤ηtarget/2):
    let S:=(rawWheelGraph P σ\permutationConflictGraph π (3*d))\JQ;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>rawWheelSpokes π d σ j v u∧¬JH v u∧¬(Sum.inr (v,u)∈K);
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    pR*β*I.card+εR*I.card+2*(εH*J.card)+
      3*(2*((3*d:ℕ):ℝ)+∑t∈Finset.Icc (i+2-buffer) i,cost t)≤ηprofile*I.card→
    (∀v∈Q.extendedVertices (i+2),|((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤ηinitial*I.card) ∧
    (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤ηinitial*I.card) ∧
    ηinitial*I.card+∑t∈Finset.Icc (i+3-buffer) i,2*cost t≤ηtarget*I.card :=by
  intro S S₀ H₀ I J hmargin
  have hh:=hAt V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hm Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs hJQ hJH havoid hgood i hi
  have hnumer:=ordinary_vortex_inner_history_budget_from_margins P D m β ε Q i buffer d pR εR εH ηinitial ηprofile ηtarget cost
    (le_trans hpmin hpR) hβ hεR hεH hcost hinit hprofile hmargin
  exact ⟨hh.1,hh.2,hnumer⟩
end Oberwolfach
