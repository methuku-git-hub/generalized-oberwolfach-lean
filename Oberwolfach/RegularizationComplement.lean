module

public import Oberwolfach.RegularizationDemands

@[expose] public section

/-! Deleted and retained edges are complementary subsets of the same
finite edge type. No parallel copies or endpoints are identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_complement_degree {E : Type*} [Fintype E]
    (P : E → Prop) (D : E → Bool) (a k : ℕ) (hk : k ≤ a)
    (htotal : (∑ e, if P e then (1 : ℕ) else 0) = a)
    (hdelete : (∑ e, if P e ∧ D e = true then (1 : ℕ) else 0) = a - k) :
    (∑ e, if P e ∧ D e = false then (1 : ℕ) else 0) = k := by
  have hadd : (∑ e, if P e ∧ D e = false then (1 : ℕ) else 0) +
      (∑ e, if P e ∧ D e = true then (1 : ℕ) else 0) = a := by
    rw [← Finset.sum_add_distrib, ← htotal]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hP : P e <;> cases hD : D e <;> simp [hP, hD]
  omega

theorem bipartiteEdges_row_degree {V : Type*} [Fintype V]
    (M : V → V → ℕ) (x : V) :
    (∑ e : BipartiteEdges M, if e.1 = x then (1 : ℕ) else 0) = ∑ y, M x y := by
  rw [← Finset.card_filter, bipartiteEdges_filter_card M (fun u _ => u = x)]
  rw [Finset.sum_comm]
  simp

theorem bipartiteEdges_column_degree {V : Type*} [Fintype V]
    (M : V → V → ℕ) (y : V) :
    (∑ e : BipartiteEdges M, if e.2.1 = y then (1 : ℕ) else 0) = ∑ x, M x y := by
  rw [← Finset.card_filter, bipartiteEdges_filter_card M (fun _ v => v = y)]
  simp

end Oberwolfach
