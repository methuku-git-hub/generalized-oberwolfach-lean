module

public import Oberwolfach.OrdinaryEditedParentFields

@[expose] public section
/-! Relaxing a wheel-load error leaves all parent data unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_edited_parent_weaken_error (r:ℕ) (hr:3≤r) (k:ℕ) (α β b B h δ ε ε':ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (d:OrdinaryEditedParentFields r hr k α β b B h δ ε P Q F H)
    (hε:ε≤ε'):
    Nonempty (OrdinaryEditedParentFields r hr k α β b B h δ ε' P Q F H):=by
  refine ⟨{d with rim_load := ?_, spoke_load := ?_}⟩
  · intro x y hxy
    exact (d.rim_load x y hxy).trans hε
  · intro v u hvu
    exact (d.spoke_load v u hvu).trans hε
end Oberwolfach
