module

public import Oberwolfach.MarkedRowPhysicalDeletionStability
public import Oberwolfach.MarkedNeighbourhoodRelationChanges
public import Oberwolfach.PhysicalSpokeDeletion

@[expose] public section

/-! Deterministic stability on the original domains for a physical deletion.
The input relations may already be modified. The same conclusion holds for
every later deletion satisfying the degree bounds, without a new event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedDeletePhysicalSpokes (H:Bool→V→U→Prop) (D:SimpleGraph (V⊕U))
    (a:Bool) (v:V) (u:U):Prop:=H a v u ∧ ¬D.Adj (Sum.inl v) (Sum.inr u)

theorem marked_spoke_physical_deletion_column_change
    (H:Bool→V→U→Prop) (D:SimpleGraph (V⊕U)) (A:Finset V) (a:Bool) (u:U):
    (∑ x∈A,if ¬(H a x u↔markedDeletePhysicalSpokes H D a x u) then (1:ℝ) else 0)
      ≤D.degree (Sum.inr u):=by
  calc
    _ ≤∑ x∈A,if D.Adj (Sum.inl x) (Sum.inr u) then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro x _
      by_cases h:H a x u <;> by_cases hd:D.Adj (Sum.inl x) (Sum.inr u) <;>
        simp [markedDeletePhysicalSpokes,h,hd]
    _ ≤∑ x:V,if D.Adj (Sum.inl x) (Sum.inr u) then (1:ℝ) else 0:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intro x _ _;positivity)
    _ = ((Finset.univ.filter (fun x=>D.Adj (Sum.inl x) (Sum.inr u))).card:ℝ):=by
      simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    _ ≤_:=Nat.cast_le.mpr (physical_spoke_deleted_col D u)

theorem marked_spoke_physical_deletion_row_change
    (H:Bool→V→U→Prop) (D:SimpleGraph (V⊕U)) (B:Finset U) (a:Bool) (v:V):
    (∑ u∈B,if ¬(H a v u↔markedDeletePhysicalSpokes H D a v u) then (1:ℝ) else 0)
      ≤D.degree (Sum.inl v):=by
  calc
    _ ≤∑ u∈B,if D.Adj (Sum.inl v) (Sum.inr u) then (1:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro u _
      by_cases h:H a v u <;> by_cases hd:D.Adj (Sum.inl v) (Sum.inr u) <;>
        simp [markedDeletePhysicalSpokes,h,hd]
    _ ≤∑ u:U,if D.Adj (Sum.inl v) (Sum.inr u) then (1:ℝ) else 0:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (by intro u _ _;positivity)
    _ = ((Finset.univ.filter (fun u=>D.Adj (Sum.inl v) (Sum.inr u))).card:ℝ):=by
      simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    _ ≤_:=Nat.cast_le.mpr (physical_spoke_deleted_row D v)

theorem marked_neighbourhoods_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (B:Finset U)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (errR errI deltaR deltaV deltaU:ℝ) (hR:0≤deltaR) (hV:0≤deltaV) (hU:0≤deltaU)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j errR σ H)
    (hi:MarkedIndicesWithSpokes π d h B q s g j errI σ H)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,(DR.degree x:ℝ)≤deltaR)
    (hrow:∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaV)
    (hcol:∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaU):
    MarkedRowsWithSpokes P π d h A p k q s g j (errR+h*(deltaR+deltaU))
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
    MarkedIndicesWithSpokes π d h B q s g j (errI+h*deltaV)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS):=by
  have hr':=markedRows_after_physical_rim_deletion P π d h A p k q s g j errR deltaR hR σ H hr DR hrim
  have hr'':=markedRows_spoke_relation_changes P π d h A p k q s g j
    (errR+h*deltaR) deltaU hU (rawMarkedDeleteRims σ DR.edgeFinset) H _ hr'
    (fun a u=>(marked_spoke_physical_deletion_column_change H DS A a u).trans (hcol u))
  have hi':=markedIndices_rim_changes π d h B q s g j errI σ (rawMarkedDeleteRims σ DR.edgeFinset) H hi
  have hi'':=markedIndices_spoke_relation_changes π d h B q s g j errI deltaV hV
    (rawMarkedDeleteRims σ DR.edgeFinset) H _ hi'
    (fun a x=>(marked_spoke_physical_deletion_row_change H DS B a x).trans (hrow x))
  refine ⟨?_,hi''⟩
  convert hr'' using 1 <;> ring

end Oberwolfach
