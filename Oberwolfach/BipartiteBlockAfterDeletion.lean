module

public import Oberwolfach.BipartiteBlockMatching
public import Oberwolfach.BipartiteCutChanges

@[expose] public section

/-! The same degree and cut bounds survive every later bounded deletion.
The lost edges are counted in the realised graph without a density factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y : Type} [Fintype X] [Fintype Y]

theorem bipartite_block_after_deletion
    (E J : X→Y→Prop) (P : X→Prop) (Q : Y→Prop)
    (d tau lam loss : ℝ) (hlam : 0≤lam)
    (H : BipartiteBlockBounds E P Q (d+loss) tau (2*lam))
    (hrow : ∀ x,((Finset.univ.filter (J x)).card:ℝ)≤loss)
    (hcol : ∀ y,((Finset.univ.filter (fun x=>J x y)).card:ℝ)≤loss)
    (hcutloss : loss≤lam*tau) :
    BipartiteBlockBounds (fun x y=>E x y ∧ ¬J x y) P Q d tau lam := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hh := degree_after_bounded_relation_deletion (fun y=>Q y ∧ E x y) (J x)
      (d+loss) loss (by convert H.row x hx using 1 <;> congr!) (hrow x)
    simp only [add_sub_cancel_right,and_assoc] at hh
    convert hh using 1 <;> congr!
  · intro y hy
    have hh := degree_after_bounded_relation_deletion (fun x=>P x ∧ E x y) (fun x=>J x y)
      (d+loss) loss (by convert H.col y hy using 1 <;> congr!) (hcol y)
    simp only [add_sub_cancel_right,and_assoc] at hh
    convert hh using 1 <;> congr!
  · intro S T hS hT hs ht
    have hold := H.cut S T hS hT hs ht
    have hchange := bipartite_cut_change_sum E (fun x y=>E x y ∧ ¬J x y) S T
    have hupper : (∑ x∈S,∑ y∈T,if ¬(E x y ↔ E x y ∧ ¬J x y) then (1:ℝ) else 0)≤
        (S.card:ℝ)*loss := by
      calc
        _ ≤ ∑ x∈S,∑ y∈T,if J x y then (1:ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          by_cases he : E x y <;> by_cases hj : J x y <;> simp [he,hj]
        _ ≤ ∑ _x∈S,loss := by
          apply Finset.sum_le_sum
          intro x hx
          apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun y hy hyt=>by positivity))
          simpa only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hrow x
        _ = _ := by simp
    have hc := (abs_le.mp (hchange.trans (by convert hupper using 1 <;> congr!))).1
    have hL := hcutloss.trans (mul_le_mul_of_nonneg_left ht hlam)
    have hLS := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg S.card)
    nlinarith only [hold,hc,hLS]

end Oberwolfach
