module

public import Oberwolfach.OrdinaryInitialDeepInnerHistoryBudget
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The cleanup margin pays the full cross window; protected older levels
contribute zero and need no accumulated deep-boundary budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_cross_window_budget_from_margins
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (i buffer d:ℕ) (pR εR εH ηinitial ηprofile ηtarget:ℝ) (cost:ℕ→ℝ)
    (hpR:0≤pR) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH)
    (hcost:∀t∈Finset.Icc (i+2-buffer) i,0≤cost t)
    (hinit:ηinitial≤ηtarget/2) (hprofile:ηprofile≤ηtarget/2):
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    let window:=Finset.Icc (i+2-buffer) i;
    pR*β*I.card+εR*I.card+2*(εH*J.card)+
      3*(2*((3*d:ℕ):ℝ)+∑t∈window,cost t)≤ηprofile*I.card→
    ηinitial*I.card+∑t∈Finset.range (i+1),
      (if t∈window then 2*cost t else 0)≤ηtarget*I.card :=by
  intro I J window hmargin
  have hbase:0≤pR*β*(I.card:ℝ)+εR*I.card+2*(εH*J.card):=by positivity
  have hnum:=ordinary_initial_deep_inner_history_budget window window cost (fun t=>2*cost t) I.card
    ηinitial ηprofile ηtarget (2*((3*d:ℕ):ℝ)) (pR*β*I.card+εR*I.card+2*(εH*J.card))
    (Finset.Subset.refl _) (by positivity) hcost (by intro t ht;exact le_rfl) (by positivity) hbase hmargin hinit hprofile
  have hfilter:(Finset.range (i+1)).filter (fun t=>t∈window)=window:=by
    ext t
    simp only [Finset.mem_filter,Finset.mem_range,window,Finset.mem_Icc]
    omega
  have hsum:(∑t∈Finset.range (i+1),if t∈window then 2*cost t else 0)=∑t∈window,2*cost t:=by
    rw [←Finset.sum_filter,hfilter]
  rw [hsum]
  exact hnum
end Oberwolfach
