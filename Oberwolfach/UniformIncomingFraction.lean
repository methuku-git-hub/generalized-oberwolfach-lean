module

public import Oberwolfach.BipartiteOneSidedRounding

@[expose] public section
/-! A head distributes its prescribed integer demand uniformly across its
eligible incoming edges. The zero-demand empty-head case uses zero weight. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Y E : Type} [Fintype Y] [Fintype E]

def eligibleIncoming (head : E → Y) (eligible : E → Prop) (y : Y) : Finset E :=
  Finset.univ.filter (fun e => eligible e ∧ head e = y)

def uniformIncomingWeight (head : E → Y) (eligible : E → Prop) (t : Y → ℕ) (e : E) : ℝ :=
  if eligible e then (t (head e):ℝ)/(eligibleIncoming head eligible (head e)).card else 0

theorem uniform_incoming_weight_bounds (head : E → Y) (eligible : E → Prop) (t : Y → ℕ)
    (ht : ∀ y, t y ≤ (eligibleIncoming head eligible y).card) (e : E) :
    0 ≤ uniformIncomingWeight head eligible t e ∧ uniformIncomingWeight head eligible t e ≤ 1 := by
  unfold uniformIncomingWeight
  split_ifs with he
  · have hle : (t (head e):ℝ) ≤ (eligibleIncoming head eligible (head e)).card := by exact_mod_cast ht (head e)
    have hn : 0 ≤ ((eligibleIncoming head eligible (head e)).card:ℝ) := by positivity
    constructor
    · exact div_nonneg (by positivity) hn
    · by_cases hzero : (eligibleIncoming head eligible (head e)).card = 0
      · simp [hzero]
      · have hpos : 0 < ((eligibleIncoming head eligible (head e)).card:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
        exact (div_le_one₀ hpos).2 hle
  · norm_num

theorem uniform_incoming_weight_columns (head : E → Y) (eligible : E → Prop) (t : Y → ℕ)
    (ht : ∀ y, t y ≤ (eligibleIncoming head eligible y).card) (y : Y) :
    (∑ e, if head e=y then uniformIncomingWeight head eligible t e else 0) = t y := by
  let S := eligibleIncoming head eligible y
  have heq : (∑ e, if head e=y then uniformIncomingWeight head eligible t e else 0) =
      ∑ e∈S, (t y:ℝ)/(S.card:ℝ) := by
    simp only [S,eligibleIncoming,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : eligible e <;> by_cases hy : head e=y <;>
      simp [S,eligibleIncoming,uniformIncomingWeight,he,hy]
  rw [heq,Finset.sum_const, nsmul_eq_mul]
  by_cases hS : S.card = 0
  · have ht0 : t y = 0 := by have hh:=ht y; change t y ≤ S.card at hh; omega
    simp [hS,ht0]
  · have hpos : (S.card:ℝ) ≠ 0 := by exact_mod_cast hS
    field_simp
end Oberwolfach
