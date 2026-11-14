module

public import Oberwolfach.LongReservedSimpleWalkEmbedding

@[expose] public section
/-! A numerical sufficient condition for the reserved-block capacity. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem sum_floor_capacity_of_slack
    {I : Type*} [Fintype I] (a : I → ℕ) (b n : ℕ)
    (hb : 0 < b) (hslack : b * (n + Fintype.card I) ≤ ∑ i, a i) :
    n ≤ ∑ i, a i / b := by
  classical
  have hp : ∀ i, a i ≤ b * (a i / b + 1) := by
    intro i
    have hm := Nat.mod_lt (a i) hb
    have hd := Nat.mod_add_div (a i) b
    nlinarith
  have hs : (∑ i, a i) ≤ ∑ i, b * (a i / b + 1) := by
    exact Finset.sum_le_sum (fun i _ => hp i)
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hs
  nlinarith
end Oberwolfach
