module

public import Oberwolfach.ExtendingListPathEmbedding
public import Oberwolfach.ExtendingListOneSidedPath

@[expose] public section
/-! A two-ended path is a one-sided path after appending its last endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem prescribed_path_through_to_from (D:V→V→Prop) (F:SimpleGraph V) (y:V):
    ∀ xs:List V,∀ x:V,DirectedPathThrough D F x y xs→
      DirectedPathFrom D F true x (xs++[y]) := by
  intro xs
  induction xs with
  | nil => intro x h;simpa [DirectedPathThrough,DirectedPathFrom] using h
  | cons z zs ih =>
    intro x h
    exact ⟨h.1,h.2.1,ih z h.2.2⟩
end Oberwolfach
