module

public import Oberwolfach.VortexInitialDomainEquivalences

@[expose] public section
/-! The initial subtype carries the original permutation under the canonical
vertex relabelling. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def vortexInitialPermutation (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V):Equiv.Perm (Q.vertices 0) where
  toFun x:=vortexInitialVertexOrderIso G D m β ε Q (π x.val)
  invFun x:=vortexInitialVertexOrderIso G D m β ε Q (π.symm x.val)
  left_inv x:=by apply Subtype.ext; simp [vortexInitialVertexOrderIso]
  right_inv x:=by apply Subtype.ext; simp [vortexInitialVertexOrderIso]

theorem vortex_initial_permutation_commutes (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V):
    ∀ x:Q.vertices 0,(vortexInitialPermutation G D m β ε Q π x).val=π x.val := by
  intro x
  rfl
end Oberwolfach
