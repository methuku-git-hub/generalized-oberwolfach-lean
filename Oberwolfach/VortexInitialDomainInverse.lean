module

public import Oberwolfach.VortexInitialPermutationPowers

@[expose] public section
/-! Canonical equivalences from the initial full vortex domains back to the
original vertex and hub types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
def vortexInitialVertexEquiv (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ)
    (Q : Vortex U G D β ε m) : Q.vertices 0 ≃ V where
  toFun x := x.val
  invFun x := vortexInitialVertexOrderIso G D m β ε Q x
  left_inv x := Subtype.ext rfl
  right_inv _ := rfl

def vortexInitialVertexOrderEmbedding (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ)
    (Q : Vortex U G D β ε m) : Q.vertices 0 ↪o V where
  toFun x := x.val
  inj' := Subtype.val_injective
  map_rel_iff' := by intro x y; rfl

theorem vortex_initial_embedding_equiv_agree (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ)
    (Q : Vortex U G D β ε m) : ∀ x,
    vortexInitialVertexEquiv G D m β ε Q x = vortexInitialVertexOrderEmbedding G D m β ε Q x := by
  intro x
  rfl

theorem vortex_initial_vertex_equiv_commutes (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ)
    (Q : Vortex U G D β ε m) (π : Equiv.Perm V) :
    ∀ x, vortexInitialVertexEquiv G D m β ε Q (vortexInitialPermutation G D m β ε Q π x) =
      π (vortexInitialVertexEquiv G D m β ε Q x) := by
  intro x
  exact vortex_initial_permutation_commutes G D m β ε Q π x
end Oberwolfach
