module

public import Oberwolfach.Vortex

@[expose] public section
/-! Canonical relabellings of the initial full vertex and hub domains. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def vortexInitialVertexOrderIso (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m):V≃o Q.vertices 0 where
  toFun v:=⟨v,by rw [Q.initial];simp⟩
  invFun v:=v.val
  left_inv _:=rfl
  right_inv _:=Subtype.ext rfl
  map_rel_iff' := by intro x y; rfl

def vortexInitialHubEquiv (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m):U≃Q.indices 0 where
  toFun u:=⟨u,by rw [Q.indices_initial];simp⟩
  invFun u:=u.val
  left_inv _:=rfl
  right_inv _:=Subtype.ext rfl

theorem vortex_initial_domain_equiv_values (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m):
    (∀ v,(vortexInitialVertexOrderIso G D m β ε Q v).val=v) ∧
    (∀ u,(vortexInitialHubEquiv G D m β ε Q u).val=u) := by
  exact ⟨fun _=>rfl,fun _=>rfl⟩
end Oberwolfach
