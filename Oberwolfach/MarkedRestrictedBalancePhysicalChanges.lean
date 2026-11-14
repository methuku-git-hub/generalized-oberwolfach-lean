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

theorem marked_restricted_degree_after_physical_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (δ:ℝ)
    (hchange:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈D.edgeFinset)
    (hD:∀ x,(D.degree x:ℝ)≤δ) (mark incoming:Bool) (v:V):
    |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
      (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δ := by
  let R:=fun x=>rawMarkedPairRims P π d σ (markedRowRim (mark,incoming,v) x)
  let R':=fun x=>rawMarkedPairRims P π d τ (markedRowRim (mark,incoming,v) x)
  have hinc: (∑ x∈A,if ¬(R x↔R' x) then (1:ℝ) else 0)≤δ := by
    calc
      _ ≤ ∑ x:V,if ¬(R x↔R' x) then (1:ℝ) else 0:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;split_ifs <;> norm_num)
      _ ≤ _ := (marked_row_rim_physical_change P π d σ τ D hchange mark incoming v).trans (hD _)
  have hh:=(indicator_sum_change A R R').trans hinc
  convert hh using 1
  apply congrArg abs
  apply congrArg₂ (fun a b:ℝ=>a-b) <;> unfold markedRestrictedDegree <;> simp only [Nat.cast_sum] <;>
    apply Finset.sum_congr rfl <;> intro x hx <;> dsimp [R,R',markedRowRim,rawMarkedPairRims] <;>
    cases mark <;> cases incoming <;> simp only [Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl,Sum.elim_inr] <;>
    norm_cast <;> symm <;> exact markedPhysicalRim_indicator _ _ _ _ _ _ _

theorem marked_restricted_balance_after_physical_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A:Finset V) (B:Finset U)
    (η δR δS:ℝ) (hR0:0≤δR) (hS0:0≤δS)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hbal:MarkedRestrictedBalanceWithSpokes P π d m A B η σ H)
    (hR:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀ v,(FR.degree v:ℝ)≤δR) (hFS:∀ z,(FS.degree z:ℝ)≤δS):
    MarkedRestrictedBalanceWithSpokes P π d m A B (η+2*δR+(m+2:ℕ)*δS) τ H' := by
  have hs:=marked_spoke_physical_change_incidence H H' FS hS
  apply marked_restricted_balance_after_arbitrary_changes P π d m A B η δR δS hR0 hS0 σ τ H H' hbal
  · exact fun mark incoming v=>marked_restricted_degree_after_physical_changes P π d A σ τ FR δR hR hFR mark incoming v
  · intro b v
    calc
      _ ≤ ∑ u:U,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (by intro x _ _;split_ifs <;> norm_num)
      _ ≤ _ := by
        have ht:=(hs.1 b v).trans (hFS (Sum.inl v))
        convert ht using 1
        apply Finset.sum_congr rfl
        intro u _
        unfold bipAdj
        split_ifs <;> simp_all
  · intro b u
    calc
      _ ≤ ∑ v:V,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;split_ifs <;> norm_num)
      _ ≤ _ := by
        have ht:=(hs.2 b u).trans (hFS (Sum.inr u))
        convert ht using 1
        apply Finset.sum_congr rfl
        intro v _
        unfold bipAdj
        split_ifs <;> simp_all
end Oberwolfach
