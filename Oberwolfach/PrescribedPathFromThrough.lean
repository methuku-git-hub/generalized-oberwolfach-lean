module

public import Oberwolfach.PrescribedPathThroughFrom

@[expose] public section
/-! Recover a two-ended path after removing its final endpoint from a
one-sided path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem prescribed_path_from_to_through (D:V→V→Prop) (F:SimpleGraph V) (y:V):
    ∀ xs:List V,∀ x:V,DirectedPathFrom D F true x (xs++[y])→
      DirectedPathThrough D F x y xs := by
  intro xs
  induction xs with
  | nil => intro x h;simpa [DirectedPathThrough,DirectedPathFrom] using h
  | cons z zs ih =>
    intro x h
    exact ⟨h.1,h.2.1,ih z h.2.2⟩
end Oberwolfach
