module

public import Oberwolfach.OrdinaryInitialDeepInnerHistoryBudget

@[expose] public section
/-! Split the cross-history budget into a recent physical-cost part, paid by
the cleanup margin, and a separately bounded older deep-boundary part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_deep_cross_history_budget
    (A B C:Finset ℕ) (cost deepCost:ℕ→ℝ) (I ηinitial ηprofile ηtarget L base:ℝ)
    (hAB:A⊆B) (hI:0≤I) (hcost:∀t∈B,0≤cost t)
    (hL:0≤L) (hbase:0≤base)
    (hmargin:base+3*(L+∑t∈B,cost t)≤ηprofile*I)
    (hinit:ηinitial≤ηtarget/4) (hprofile:ηprofile≤ηtarget/4)
    (hold:(∑t∈C,if t∈A then 0 else 2*deepCost t)≤(ηtarget/2)*I):
    ηinitial*I+∑t∈C,(if t∈A then 2*cost t else 2*deepCost t)≤ηtarget*I :=by
  let W:=C.filter (fun t=>t∈A)
  have hWB:W⊆B:=by
    intro t ht
    exact hAB (Finset.mem_filter.mp ht).2
  have hnew:=ordinary_initial_deep_inner_history_budget W B cost (fun t=>2*cost t) I
    ηinitial ηprofile (ηtarget/2) L base hWB hI hcost (by intro t ht;exact le_rfl) hL hbase hmargin
    (by linarith [hinit]) (by linarith [hprofile])
  have hsplit:(∑t∈C,(if t∈A then 2*cost t else 2*deepCost t))=
      (∑t∈W,2*cost t)+(∑t∈C,if t∈A then 0 else 2*deepCost t):=by
    rw [Finset.sum_filter]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> simp_all
  rw [hsplit]
  linarith
end Oberwolfach
