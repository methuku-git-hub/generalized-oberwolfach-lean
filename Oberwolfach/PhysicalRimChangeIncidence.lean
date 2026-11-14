module

public import Oberwolfach.MarkedPotentialPhysicalDeletion

@[expose] public section
/-! An arbitrary change of typed rim relations controlled by a physical
edge deletion has bounded incidence in both auxiliary directions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem physical_rim_change_incidence
    (π:Equiv.Perm V) (D:SimpleGraph V) (δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (R R':(V×V)⊕(V×V)→Prop)
    (hchange:∀e,¬(R e↔R' e)→markedPairPhysical π e∈D.edgeFinset):
    (∀x,(∑e,if ¬(R e↔R' e) ∧ Sum.elim Prod.fst Prod.fst e=x then (1:ℝ) else 0)≤2*δ) ∧
    (∀x,(∑e,if ¬(R e↔R' e) ∧ Sum.elim Prod.snd Prod.snd e=x then (1:ℝ) else 0)≤2*δ) :=by
  have hrow (mark incoming:Bool) (x:V):
      (∑y:V,if ¬(R (markedRowRim (mark,incoming,x) y)↔R' (markedRowRim (mark,incoming,x) y)) then (1:ℝ) else 0)≤δ:=by
    calc
      _ ≤ ∑y:V,if markedPairPhysical π (markedRowRim (mark,incoming,x) y)∈D.edgeFinset then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum
        intro y _
        by_cases h:¬(R (markedRowRim (mark,incoming,x) y)↔R' (markedRowRim (mark,incoming,x) y))
        · simp [h,hchange _ h]
        · simp only [h,ite_false]
          split_ifs <;> norm_num
      _ = D.degree (if mark && incoming then π x else x):=marked_row_physical_coordinate_degree π D mark incoming x
      _ ≤ δ:=hD _
  constructor
  · intro x
    have h0:=hrow false false x
    have h1:=hrow true false x
    calc
      _ ≤ δ+δ:=by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · convert h0 using 1
          convert pair_indicator_sum_at_first (fun e=>¬(R (Sum.inl e)↔R' (Sum.inl e))) x using 1 <;>
            (apply Finset.sum_congr rfl; intro z _; (try simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]); split_ifs <;> rfl)
        · convert h1 using 1
          convert pair_indicator_sum_at_first (fun e=>¬(R (Sum.inr e)↔R' (Sum.inr e))) x using 1 <;>
            (apply Finset.sum_congr rfl; intro z _; (try simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]); split_ifs <;> rfl)
      _ = _:=by ring
  · intro x
    have h0:=hrow false true x
    have h1:=hrow true true x
    calc
      _ ≤ δ+δ:=by
        rw [Fintype.sum_sum_type]
        apply add_le_add
        · convert h0 using 1
          convert pair_indicator_sum_at_second (fun e=>¬(R (Sum.inl e)↔R' (Sum.inl e))) x using 1 <;>
            (apply Finset.sum_congr rfl; intro z _; (try simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]); split_ifs <;> rfl)
        · convert h1 using 1
          convert pair_indicator_sum_at_second (fun e=>¬(R (Sum.inr e)↔R' (Sum.inr e))) x using 1 <;>
            (apply Finset.sum_congr rfl; intro z _; (try simp only [markedRowRim,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true]); split_ifs <;> rfl)
      _ = _:=by ring
end Oberwolfach
