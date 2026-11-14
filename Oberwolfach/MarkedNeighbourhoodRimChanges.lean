module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section

/-! Deterministic changes of the rim predicates preserve the original
row domain, comparison target and coefficients. The hypothesis counts
changes at every ambient root, not only roots inside the tested domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedRowCountWithSpokes_rim_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (A C:Finset V) (hCA:C⊆A) (S:Finset (Bool×Bool×V)) (J:Finset (Bool×U)) (delta:ℝ)
    (hchange:∀ a∈S,(∑ x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
      rawMarkedPairRims P π d τ (markedRowRim a x)) then (1:ℝ) else 0)≤delta):
    |markedRowCountWithSpokes P π d τ H C S J-markedRowCountWithSpokes P π d σ H C S J|≤S.card*delta:=by
  have hh:=finiteConjunction_sum_change_at_outer A C hCA S (fun x=>∀ a∈J,H a.1 x a.2)
    (fun a x=>rawMarkedPairRims P π d σ (markedRowRim a x))
    (fun a x=>rawMarkedPairRims P π d τ (markedRowRim a x)) delta hchange
  convert hh using 1
  apply congrArg abs
  apply congrArg₂ (fun x y:ℝ=>x-y)
  all_goals
    unfold markedRowCountWithSpokes
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> first | rfl | tauto

theorem markedRows_rim_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err delta:ℝ) (hdelta:0≤delta)
    (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j err σ H)
    (hchange:∀ a:Bool×Bool×V,(∑ x∈A,if ¬(rawMarkedPairRims P π d σ (markedRowRim a x)↔
      rawMarkedPairRims P π d τ (markedRowRim a x)) then (1:ℝ) else 0)≤delta):
    MarkedRowsWithSpokes P π d h A p k q s g j (err+h*delta) τ H:=by
  intro S T J hS hT hJ hinj
  let C:=markedRowDomain P π (3*d) A S T
  have hc:=markedRowCountWithSpokes_rim_change P π d σ τ H A C (Finset.filter_subset _ _) S J delta
    (fun a _=>hchange a)
  have hcard:(S.card:ℝ)≤h:=by exact_mod_cast hS
  have he:=hr S T J hS hT hJ hinj
  have hbound:=hc.trans (mul_le_mul_of_nonneg_right hcard hdelta)
  have hh:=(abs_sub_le (markedRowCountWithSpokes P π d τ H C S J)
    (markedRowCountWithSpokes P π d σ H C S J)
    ((∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*C.card)).trans_lt
      (add_lt_add_of_le_of_lt hbound he)
  convert hh using 1 <;> ring

theorem markedIndices_rim_changes
    (π:Equiv.Perm V) (d h:ℕ) (B:Finset U)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hi:MarkedIndicesWithSpokes π d h B q s g j err σ H):
    MarkedIndicesWithSpokes π d h B q s g j err τ H:=hi

end Oberwolfach
