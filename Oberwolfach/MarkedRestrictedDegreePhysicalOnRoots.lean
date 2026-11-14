module

public import Oberwolfach.MarkedRestrictedBalanceArbitraryChanges
public import Oberwolfach.MarkedModifiedPhysicalIncidence
public import Oberwolfach.MarkedSampleOccurrenceMatrix

@[expose] public section
/-! Charge changes in restricted balance to realised physical degrees,
without assuming that any root lies in the summation domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_restricted_degree_after_physical_changes_on_roots
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (δ:ℝ)
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈D.edgeFinset)
    (Roots:Finset V) (hRoots:∀x,x∈Roots→π x∈Roots)
    (hD:∀x∈Roots,(D.degree x:ℝ)≤δ) (mark incoming:Bool) (v:V) (hv:v∈Roots):
    |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
      (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δ := by
  let R:=fun x=>rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)
  let R':=fun x=>rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x)
  have hinc: (∑ x∈A,if ¬(R x↔R' x) then (1:ℝ) else 0)≤δ := by
    calc
      _ ≤ ∑ x:V,if ¬(R x↔R' x) then (1:ℝ) else 0:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;split_ifs <;> norm_num)
      _ ≤ _ := (marked_row_rim_physical_change P π d σ τ D hchange mark incoming v).trans
        (hD _ (by split_ifs <;> first | exact hRoots v hv | exact hv))
  have hh:=(indicator_sum_change A R R').trans hinc
  convert hh using 1
  apply congrArg abs
  apply congrArg₂ (fun a b:ℝ=>a-b) <;> unfold markedRestrictedDegree <;> simp only [Nat.cast_sum] <;>
    apply Finset.sum_congr rfl <;> intro x hx <;> dsimp [R,R',markedRowRim,rawMarkedPairRims] <;>
    cases mark <;> cases incoming <;> simp only [Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr] <;>
    norm_cast <;> symm <;> exact markedPhysicalRim_indicator _ _ _ _ _ _ _

end Oberwolfach
