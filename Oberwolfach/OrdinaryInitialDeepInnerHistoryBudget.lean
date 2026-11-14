module

public import Oberwolfach.OrdinaryInitialDeepBalanceOrderedChoice

@[expose] public section
/-! The initial margin and the deep cleanup margin automatically pay for
all recent wheel-boundary discrepancies controlled by twice their costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_deep_inner_history_budget
    (A B:Finset ℕ) (cost boundary:ℕ→ℝ) (I ηinitial ηprofile ηtarget L base:ℝ)
    (hAB:A⊆B) (hI:0≤I) (hcost:∀t∈B,0≤cost t)
    (hboundary:∀t∈A,boundary t≤2*cost t)
    (hL:0≤L) (hbase:0≤base)
    (hmargin:base+3*(L+∑t∈B,cost t)≤ηprofile*I)
    (hinit:ηinitial≤ηtarget/2) (hprofile:ηprofile≤ηtarget/2):
    ηinitial*I+∑t∈A,boundary t≤ηtarget*I :=by
  have hsA:(∑t∈A,boundary t)≤∑t∈A,2*cost t:=Finset.sum_le_sum (by intro t ht;exact hboundary t ht)
  have hsAB:(∑t∈A,2*cost t)≤∑t∈B,2*cost t:=
    Finset.sum_le_sum_of_subset_of_nonneg hAB (by intro t ht _;have hh:=hcost t ht;positivity)
  have hs0:0≤∑t∈B,cost t:=Finset.sum_nonneg (by intro t ht;exact hcost t ht)
  have hs:∑t∈B,2*cost t=2*∑t∈B,cost t:=by rw [Finset.mul_sum]
  have hi:=mul_le_mul_of_nonneg_right hinit hI
  have hp:=mul_le_mul_of_nonneg_right hprofile hI
  rw [hs] at hsAB
  nlinarith only [hsA,hsAB,hs0,hL,hbase,hmargin,hi,hp]
end Oberwolfach
