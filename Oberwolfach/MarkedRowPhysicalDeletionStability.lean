module

public import Oberwolfach.RawMarkedRimDeletion
public import Oberwolfach.MarkedNeighbourhoodRimChanges

@[expose] public section

/-! Full ambient-root row estimates after an actual physical rim deletion.
Incoming marked roots are charged at π(v). The original domain, coefficients
and target are fixed, and the bound is deterministic for every later D. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_row_physical_coordinate_degree
    (π:Equiv.Perm V) (D:SimpleGraph V) (mark incoming:Bool) (v:V):
    (∑ x:V,if markedPairPhysical π (markedRowRim (mark,incoming,v) x)∈D.edgeFinset then (1:ℝ) else 0)=
      D.degree (if mark && incoming then π v else v):=by
  have hsum (z:V):(∑ x:V,if D.Adj z x then (1:ℝ) else 0)=D.degree z:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_eq_filter]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hsumπ (z:V):(∑ x:V,if D.Adj z (π x) then (1:ℝ) else 0)=D.degree z:=
    (Equiv.sum_comp π (fun x=>if D.Adj z x then (1:ℝ) else 0)).trans (hsum z)
  cases mark <;> cases incoming <;>
    simp only [markedRowRim,markedPairPhysical,Bool.false_eq_true,ite_false,ite_true,
      Sum.elim_inl,Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
      Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true]
  · exact hsum v
  · simpa [D.adj_comm] using hsum v
  · exact hsumπ v
  · simpa [D.adj_comm] using hsum (π v)

theorem marked_row_rim_physical_deletion_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:SimpleGraph V) (A:Finset V) (a:Bool×Bool×V):
    (∑ x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
      rawMarkedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset) (markedRowRim a x)) then (1:ℝ) else 0)
      ≤D.degree (if a.1 && a.2.1 then π a.2.2 else a.2.2):=by
  calc
    _ ≤ ∑ x∈A,if markedPairPhysical π (markedRowRim a x)∈D.edgeFinset then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro x _
      rw [rawMarkedDeleteRims_rims]
      by_cases he:rawMarkedPairRims P π d σ (markedRowRim a x) <;>
        by_cases hd:markedPairPhysical π (markedRowRim a x)∈D.edgeFinset <;> simp [he,hd]
    _ ≤ ∑ x:V,if markedPairPhysical π (markedRowRim a x)∈D.edgeFinset then (1:ℝ) else 0:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;positivity)
    _ = _:=marked_row_physical_coordinate_degree π D a.1 a.2.1 a.2.2

theorem markedRows_after_physical_rim_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err delta:ℝ) (hdelta:0≤delta)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j err σ H)
    (D:SimpleGraph V) (hD:∀ x,(D.degree x:ℝ)≤delta):
    MarkedRowsWithSpokes P π d h A p k q s g j (err+h*delta) (rawMarkedDeleteRims σ D.edgeFinset) H:=by
  apply markedRows_rim_changes P π d h A p k q s g j err delta hdelta σ _ H hr
  intro a
  exact (marked_row_rim_physical_deletion_change P π d σ D A a).trans (hD _)

end Oberwolfach
