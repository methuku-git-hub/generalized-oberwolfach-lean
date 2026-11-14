module

public import Oberwolfach.PrescribedPathScheduleEdges

@[expose] public section
/-! Split an ordered vertex list at each missing consecutive edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

def splitOrderedPath (keep:V→V→Bool):List V→List (List V)
  | [] => []
  | [x] => [[x]]
  | x::y::xs =>
    let rest:=splitOrderedPath keep (y::xs)
    if keep x y then
      match rest with
      | [] => [[x]]
      | block::blocks => (x::block)::blocks
    else [x]::rest

theorem split_ordered_path_head (keep:V→V→Bool):
    ∀ x:V,∀ xs:List V,∃ block blocks,splitOrderedPath keep (x::xs)=(x::block)::blocks := by
  intro x xs
  induction xs generalizing x with
  | nil => exact ⟨[],[],rfl⟩
  | cons y ys ih =>
    obtain ⟨block,blocks,h⟩:=ih y
    simp only [splitOrderedPath,h]
    cases hk:keep x y <;> simp [hk]

theorem split_ordered_path_flatten (keep:V→V→Bool):
    ∀ xs:List V,(splitOrderedPath keep xs).flatten=xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      obtain ⟨block,blocks,h⟩:=split_ordered_path_head keep y ys
      simp only [splitOrderedPath,h]
      rw [h] at ih
      cases hk:keep x y <;> simp_all [hk]
end Oberwolfach
