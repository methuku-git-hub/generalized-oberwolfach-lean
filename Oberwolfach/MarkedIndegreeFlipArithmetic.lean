module

public import Oberwolfach.UniformIncomingRounded

@[expose] public section
/-! Exact marked-indegree change when the selected arcs at a given head are
all of the same original type. Directions and the edge set are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Y E : Type} [Fintype E]

def flipMarkedArcs (M D:E→Bool) (e:E) : Bool := if D e then !M e else M e

theorem marked_indegree_flip_reduces (head:E→Y) (M D:E→Bool) (y:Y)
    (h : ∀ e, head e=y → D e=true → M e=true) :
    (∑ e, if head e=y ∧ flipMarkedArcs M D e=true then (1:ℤ) else 0) =
    (∑ e, if head e=y ∧ M e=true then (1:ℤ) else 0) -
      (∑ e, if head e=y ∧ D e=true then (1:ℤ) else 0) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hy : head e=y
  · cases hm : M e <;> cases hd : D e <;>
      simp_all [flipMarkedArcs]
  · simp [hy]

theorem marked_indegree_flip_increases (head:E→Y) (M D:E→Bool) (y:Y)
    (h : ∀ e, head e=y → D e=true → M e=false) :
    (∑ e, if head e=y ∧ flipMarkedArcs M D e=true then (1:ℤ) else 0) =
    (∑ e, if head e=y ∧ M e=true then (1:ℤ) else 0) +
      (∑ e, if head e=y ∧ D e=true then (1:ℤ) else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hy : head e=y
  · cases hm : M e <;> cases hd : D e <;>
      simp_all [flipMarkedArcs]
  · simp [hy]
end Oberwolfach
