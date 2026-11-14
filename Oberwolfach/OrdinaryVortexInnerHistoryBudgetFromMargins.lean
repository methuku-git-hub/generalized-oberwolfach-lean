module

public import Oberwolfach.OrdinaryInitialDeepInnerHistoryBudget

@[expose] public section
/-! The actual buffered-vortex cleanup margin pays the coarse recent
inner-boundary cost, leaving room for the protected initial imbalance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_inner_history_budget_from_margins
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (i buffer d:ℕ) (pR εR εH ηinitial ηprofile ηtarget:ℝ) (cost:ℕ→ℝ)
    (hpR:0≤pR) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH)
    (hcost:∀t∈Finset.Icc (i+2-buffer) i,0≤cost t)
    (hinit:ηinitial≤ηtarget/2) (hprofile:ηprofile≤ηtarget/2):
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    pR*β*I.card+εR*I.card+2*(εH*J.card)+
      3*(2*((3*d:ℕ):ℝ)+∑t∈Finset.Icc (i+2-buffer) i,cost t)≤ηprofile*I.card→
    ηinitial*I.card+∑t∈Finset.Icc (i+3-buffer) i,2*cost t≤ηtarget*I.card :=by
  intro I J hmargin
  have hAB:Finset.Icc (i+3-buffer) i ⊆ Finset.Icc (i+2-buffer) i:=by
    intro t ht
    simp only [Finset.mem_Icc] at ht ⊢
    omega
  have hbase:0≤pR*β*(I.card:ℝ)+εR*I.card+2*(εH*J.card):=by positivity
  exact ordinary_initial_deep_inner_history_budget _ _ cost (fun t=>2*cost t) I.card
    ηinitial ηprofile ηtarget (2*((3*d:ℕ):ℝ)) (pR*β*I.card+εR*I.card+2*(εH*J.card))
    hAB (by positivity) hcost (by intro t ht;exact le_rfl) (by positivity) hbase hmargin hinit hprofile
end Oberwolfach
