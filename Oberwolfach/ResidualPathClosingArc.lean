module

public import Oberwolfach.ResidualRetainedPathArcs
public import Oberwolfach.ResidualPathClosingEdge

@[expose] public section
/-! Appending the initial vertex adds exactly the closing directed arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem ordered_path_append_closing_arc:
    ∀ (xs:List V) (a u:V),xs.getLast?=some u→
      prescribedDirectedPathEdges (xs++[a])=
        insert (u,a) (prescribedDirectedPathEdges xs) := by
  intro xs
  induction xs with
  | nil => intro a u h;simp at h
  | cons x xs ih =>
    intro a u h
    cases xs with
    | nil =>
      simp at h
      subst u
      simp [prescribedDirectedPathEdges]
    | cons y ys =>
      have ht:(y::ys).getLast?=some u := by simpa using h
      have hh:=ih a u ht
      simp only [List.cons_append] at hh
      simp only [List.cons_append,prescribedDirectedPathEdges]
      rw [hh]
      exact Finset.insert_comm _ _ _
end Oberwolfach
