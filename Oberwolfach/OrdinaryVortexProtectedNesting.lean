module

public import Oberwolfach.VortexExtended

@[expose] public section
/-! The ordinary protected trace uses consecutive and next-consecutive
vortex levels; the required older-level containment is automatic. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U]

theorem ordinary_vortex_protected_nesting
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (i:ℕ):
    (∀j < i,Q.extendedVertices (i+1)⊆Q.extendedVertices (j+2)) ∧
    (∀j < i,Q.extendedIndices (i+1)⊆Q.extendedIndices (j+2)):=by
  constructor
  · intro j hj
    exact Q.extendedVertices_subset (by omega)
  · intro j hj
    exact Q.extendedIndices_subset (by omega)
end Oberwolfach
