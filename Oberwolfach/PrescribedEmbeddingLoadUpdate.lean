module

public import Oberwolfach.SaturatedVertexBound

@[expose] public section
/-! A greedy assignment keeps the claimed load bound after each choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [DecidableEq V]

theorem prescribed_embedding_load_update (f:V→ℕ) (t:ℝ) (x:V)
    (hbound:∀ v,(f v:ℝ)≤t+1) (hfree:(f x:ℝ)<t):
    ∀ v,((Function.update f x (f x+1) v:ℕ):ℝ)≤t+1 := by
  intro v
  by_cases hv:v=x
  · subst v
    simp only [Function.update_self, Nat.cast_add, Nat.cast_one]
    linarith
  · simp only [Function.update_of_ne hv]
    exact hbound v
end Oberwolfach
