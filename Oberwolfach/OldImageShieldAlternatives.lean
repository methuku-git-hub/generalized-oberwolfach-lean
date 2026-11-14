module

public import Oberwolfach.EdgeAssignmentToPhysical

@[expose] public section
/-! Old-image exclusion may be enforced either by the edge lists or by
forbidden indices at the endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem old_image_shield_from_forbidden (G:SimpleGraph V) (L:Sym2 V→Finset I) (Bad:V→Finset I) (Old:I→Finset V)
    (hBad:∀i v,v∈Old i→i∈Bad v):
    ∀i e v,e∈G.edgeFinset→v∈e.toFinset→v∈Old i→i∈L e→i∈Bad v := by
  intro i e v he hv hOld hi
  exact hBad i v hOld

theorem old_image_shield_from_lists (G:SimpleGraph V) (L:Sym2 V→Finset I) (Bad:V→Finset I) (Old:I→Finset V)
    (hLists:∀i e v,e∈G.edgeFinset→v∈e.toFinset→v∈Old i→i∉L e):
    ∀i e v,e∈G.edgeFinset→v∈e.toFinset→v∈Old i→i∈L e→i∈Bad v := by
  intro i e v he hv hOld hi
  exact ((hLists i e v he hv hOld) hi).elim
end Oberwolfach
