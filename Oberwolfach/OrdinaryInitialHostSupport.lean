module

public import Oberwolfach.OrdinaryVortexSupportedHostFineCover

@[expose] public section
/-! The initial vortex parent contains every row and hub, so any actual
remainder is supported there. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_host_support
    {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P G : SimpleGraph V) (Hs : V → U → Prop) (D m : ℕ) (β ε : ℝ)
    (Q : Vortex U P D β ε m) :
    ordinaryHostResources G Hs ⊆ ordinaryRootResources (Q.extendedVertices 0) (Q.extendedIndices 0) := by
  apply ordinaryRootResources_contains
  · rw [Q.extendedVertices_eq (Nat.zero_le _), Q.initial]
    exact Finset.subset_univ _
  · rw [Q.extendedIndices_eq (Nat.zero_le _), Q.indices_initial]
    exact Finset.subset_univ _
end Oberwolfach
