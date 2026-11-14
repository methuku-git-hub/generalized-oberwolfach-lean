module

public import Oberwolfach.PrescribedTargetMatching

@[expose] public section
/-! Inner indices carry single prescribed labels, and matching edges are
assigned only to outside indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [DecidableEq I] [DecidableEq V]

theorem prescribed_inner_outer_disjoint (inner:Finset I) (M:I→Finset (V×V)) (Z:I→Finset V)
    (hinner:∀i,i∈inner→M i=∅) (houter:∀i,i∉inner→Z i=∅):
    ∀i,Disjoint (prescribedMatchingEndpoints (M i)) (Z i):=by
  intro i
  by_cases hi:i∈inner
  · rw [hinner i hi]
    simp [prescribedMatchingEndpoints]
  · rw [houter i hi]
    simp
end Oberwolfach
