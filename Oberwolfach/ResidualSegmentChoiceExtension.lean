module

public import Oberwolfach.ResidualActualPrescribedSet

@[expose] public section
/-! Extend selected-segment sets by the empty set outside the selected
path family, without changing any selected path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [DecidableEq I]

def extendSelectedSegments (s:Finset I) (T:I→Finset ℕ) (i:I):Finset ℕ :=
  if i∈s then T i else ∅

theorem extend_selected_segments_bounded (s:Finset I) (T:I→Finset ℕ)
    (d:ℕ) (hT:∀i∈s,T i⊆Finset.range d):
    ∀ i,extendSelectedSegments s T i⊆Finset.range d := by
  intro i
  by_cases hi:i∈s
  · simpa [extendSelectedSegments,hi] using hT i hi
  · simp [extendSelectedSegments,hi]

theorem extend_selected_segments_agrees (s:Finset I) (T:I→Finset ℕ)
    (i:I) (hi:i∈s):extendSelectedSegments s T i=T i := by
  simp [extendSelectedSegments,hi]
end Oberwolfach
