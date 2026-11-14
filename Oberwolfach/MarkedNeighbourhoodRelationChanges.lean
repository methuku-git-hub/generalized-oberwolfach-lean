module

public import Oberwolfach.MarkedNeighbourhoodRimChanges

@[expose] public section

/-! Change arbitrary current spoke relations on the original fixed domains.
The original comparison products and all ambient root quantifiers remain
unchanged. These estimates apply after earlier deterministic modifications. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedRowCountWithSpokes_relation_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H H':Bool→V→U→Prop) (A C:Finset V) (hCA:C⊆A)
    (S:Finset (Bool×Bool×V)) (J:Finset (Bool×U)) (delta:ℝ)
    (hchange:∀ a∈J,(∑ x∈A,if ¬(H a.1 x a.2↔H' a.1 x a.2) then (1:ℝ) else 0)≤delta):
    |markedRowCountWithSpokes P π d σ H' C S J-markedRowCountWithSpokes P π d σ H C S J|≤J.card*delta:=by
  have hh:=finiteConjunction_sum_change_at_outer A C hCA J
    (fun x=>∀ a∈S,rawMarkedPairRims P π d σ (markedRowRim a x))
    (fun a x=>H a.1 x a.2) (fun a x=>H' a.1 x a.2) delta hchange
  convert hh using 1 <;> unfold markedRowCountWithSpokes <;> congr!

theorem markedRows_spoke_relation_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err delta:ℝ) (hdelta:0≤delta)
    (σ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h A p k q s g j err σ H)
    (hchange:∀ a u,(∑ x∈A,if ¬(H a x u↔H' a x u) then (1:ℝ) else 0)≤delta):
    MarkedRowsWithSpokes P π d h A p k q s g j (err+h*delta) σ H':=by
  intro S T J hS hT hJ hinj
  let C:=markedRowDomain P π (3*d) A S T
  have hc:=markedRowCountWithSpokes_relation_change P π d σ H H' A C (Finset.filter_subset _ _) S J delta
    (fun a _=>hchange a.1 a.2)
  have hcard:(J.card:ℝ)≤h:=by exact_mod_cast hJ
  have he:=hr S T J hS hT hJ hinj
  have hbound:=hc.trans (mul_le_mul_of_nonneg_right hcard hdelta)
  have hh:=(abs_sub_le (markedRowCountWithSpokes P π d σ H' C S J)
    (markedRowCountWithSpokes P π d σ H C S J)
    ((∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*C.card)).trans_lt
      (add_lt_add_of_le_of_lt hbound he)
  convert hh using 1 <;> ring

theorem markedIndices_spoke_relation_changes
    (π:Equiv.Perm V) (d h:ℕ) (B:Finset U)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (err delta:ℝ) (hdelta:0≤delta)
    (σ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hi:MarkedIndicesWithSpokes π d h B q s g j err σ H)
    (hchange:∀ a x,(∑ u∈B,if ¬(H a x u↔H' a x u) then (1:ℝ) else 0)≤delta):
    MarkedIndicesWithSpokes π d h B q s g j (err+h*delta) σ H':=by
  intro J hJ hsep
  have hh:=finiteConjunction_sum_change_at_outer B B (fun _ h=>h) J (fun _=>True)
    (fun a u=>H a.1 a.2 u) (fun a u=>H' a.1 a.2 u) delta (fun a _=>hchange a.1 a.2)
  have hc:|markedIndexCountWithSpokes H' B J-markedIndexCountWithSpokes H B J|≤J.card*delta:=by
    convert hh using 1 <;> simp only [markedIndexCountWithSpokes,true_and] <;> congr!
  have hcard:(J.card:ℝ)≤h:=by exact_mod_cast hJ
  have he:=hi J hJ hsep
  have hbound:=hc.trans (mul_le_mul_of_nonneg_right hcard hdelta)
  have ht:=(abs_sub_le (markedIndexCountWithSpokes H' B J) (markedIndexCountWithSpokes H B J)
    (∑ u∈B,∏ a∈J,if a.1 then q u g else s u j)).trans_lt
      (add_lt_add_of_le_of_lt hbound he)
  convert ht using 1 <;> ring

end Oberwolfach
