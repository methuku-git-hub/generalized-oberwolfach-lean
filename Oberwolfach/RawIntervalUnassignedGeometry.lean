module

public import Oberwolfach.RawIntervalGeometry

@[expose] public section
/-! The unassigned state excludes covered interval labels and assigned
ordinary labels, while it includes uncovered successor endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Γ Color:Type} [Fintype V] [DecidableEq V]

theorem rawIntervalState_none_iff (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalOutcome V Γ Color) (x:V):
    rawIntervalState π d σ x=none ↔
      (∀ g,¬rawIntervalCovered π d σ x g) ∧
      (rawIntervalBlocked π d σ x ∨ σ (Sum.inr (Sum.inr x))=none) := by
  by_cases hg:∃ g,rawIntervalCovered π d σ x g
  · simp only [rawIntervalState,dif_pos hg,Option.some_ne_none,false_iff]
    intro h
    obtain ⟨g,hg⟩:=hg
    exact h.1 g hg
  · have hg':∀ g,¬rawIntervalCovered π d σ x g:=fun g h=>hg ⟨g,h⟩
    by_cases hb:rawIntervalBlocked π d σ x
    · simp [rawIntervalState,hg,hg',hb]
    · cases hc:σ (Sum.inr (Sum.inr x)) <;> simp [rawIntervalState,hg,hg',hb,hc]
end Oberwolfach
