module

public import Oberwolfach.PrescribedPathScheduleEdges
public import Oberwolfach.PrescribedFreePathPhysicalEdges
public import Oberwolfach.PrescribedPathPhysicalEdges

@[expose] public section
/-! Connect the schedule's ordered-edge sets with the component update sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_ordered_one_sided_edges:
    ∀ (as:List X) (a:X),prescribedOrderedPathEdges (a::as)=prescribedOneSidedPhysicalEdges a as := by
  intro as
  induction as with
  | nil => intro a;rfl
  | cons x xs ih => intro a;simp [prescribedOrderedPathEdges,prescribedOneSidedPhysicalEdges,ih]

theorem prescribed_ordered_two_sided_edges:
    ∀ (as:List X) (a b:X),prescribedOrderedPathEdges (a::as++[b])=prescribedPathPhysicalEdges a b as := by
  intro as
  induction as with
  | nil => intro a b;simp [prescribedOrderedPathEdges,prescribedPathPhysicalEdges]
  | cons x xs ih =>
    intro a b
    simp only [List.cons_append,prescribedOrderedPathEdges,prescribedPathPhysicalEdges]
    simp only [List.cons_append] at ih
    rw [ih]

theorem prescribed_ordered_free_path_edges (as:List X):
    prescribedOrderedPathEdges as=prescribedFreePathPhysicalEdges as := by
  cases as with
  | nil => rfl
  | cons a as => exact prescribed_ordered_one_sided_edges as a
theorem prescribed_ordered_two_end_reverse:
    ∀ (xs:List X) (a b:X),
      prescribedOrderedPathEdges (a::xs++[b]) =
      prescribedOrderedPathEdges (b::(a::xs).reverse) := by
  intro xs
  induction xs with
  | nil =>
    intro a b
    simp [prescribedOrderedPathEdges,Sym2.eq_swap]
  | cons x xs ih =>
    intro a b
    simp only [List.cons_append,prescribedOrderedPathEdges,List.reverse_cons]
    have hp:=prescribed_path_edges_pivot x [a] (b::xs.reverse)
    simp only [List.cons_append] at ih
    rw [ih x b]
    simp only [List.cons_append] at hp
    simp [prescribedOrderedPathEdges,Sym2.eq_swap,Finset.union_comm,Finset.insert_union] at hp ⊢
    exact hp.symm

theorem prescribed_ordered_right_sided_edges (as:List X) (b:X):
    prescribedOrderedPathEdges (as++[b])=prescribedOneSidedPhysicalEdges b as.reverse := by
  cases as with
  | nil => simp [prescribedOrderedPathEdges,prescribedOneSidedPhysicalEdges]
  | cons a xs =>
    rw [prescribed_ordered_two_end_reverse]
    exact prescribed_ordered_one_sided_edges _ b
end Oberwolfach
