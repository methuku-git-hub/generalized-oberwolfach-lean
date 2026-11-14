module

public import Oberwolfach.OrdinaryInitialDeepCrossHistoryBudget
public import Oberwolfach.OrdinaryVortexInnerHistoryBudgetFromMargins

@[expose] public section
/-! On the buffered vortex, the cleanup margin pays the recent cross cost;
only the explicitly displayed older deep-boundary budget remains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_cross_history_budget_from_margins
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (i buffer d:ℕ) (pR εR εH ηinitial ηprofile ηtarget:ℝ) (cost deepCost:ℕ→ℝ)
    (hpR:0≤pR) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH)
    (hcost:∀t∈Finset.Icc (i+2-buffer) i,0≤cost t)
    (hinit:ηinitial≤ηtarget/4) (hprofile:ηprofile≤ηtarget/4):
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    pR*β*I.card+εR*I.card+2*(εH*J.card)+
      3*(2*((3*d:ℕ):ℝ)+∑t∈Finset.Icc (i+2-buffer) i,cost t)≤ηprofile*I.card→
    (∑t∈Finset.range (i+1),if t∈Finset.Icc (i+3-buffer) i then 0 else 2*deepCost t)≤(ηtarget/2)*I.card→
    ηinitial*I.card+∑t∈Finset.range (i+1),
      (if t∈Finset.Icc (i+3-buffer) i then 2*cost t else 2*deepCost t)≤ηtarget*I.card :=by
  intro I J hmargin hold
  have hAB:Finset.Icc (i+3-buffer) i ⊆ Finset.Icc (i+2-buffer) i:=by
    intro t ht
    simp only [Finset.mem_Icc] at ht ⊢
    omega
  have hbase:0≤pR*β*(I.card:ℝ)+εR*I.card+2*(εH*J.card):=by positivity
  exact ordinary_initial_deep_cross_history_budget _ _ _ cost deepCost I.card
    ηinitial ηprofile ηtarget (2*((3*d:ℕ):ℝ)) (pR*β*I.card+εR*I.card+2*(εH*J.card))
    hAB (by positivity) hcost (by positivity) hbase hmargin hinit hprofile hold
end Oberwolfach
