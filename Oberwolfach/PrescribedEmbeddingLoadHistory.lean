module

public import Oberwolfach.PrescribedEmbeddingLoadUpdate

@[expose] public section
/-! Saturation is enforced at every sequential vertex assignment. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [DecidableEq V]

def updateLoads (f:V→ℕ):List V→(V→ℕ)
  | []=>f
  | x::xs=>updateLoads (Function.update f x (f x+1)) xs

def respectsLoadLimit (t:ℝ) (f:V→ℕ):List V→Prop
  | []=>True
  | x::xs=>(f x:ℝ)<t ∧ respectsLoadLimit t (Function.update f x (f x+1)) xs

theorem prescribed_embedding_load_history_bound (t:ℝ) :
    ∀ xs:List V,∀ f:V→ℕ,(∀ v,(f v:ℝ)≤t+1)→ respectsLoadLimit t f xs→
      ∀ v,(updateLoads f xs v:ℝ)≤t+1 := by
  intro xs
  induction xs with
  | nil => intro f hf _ v;exact hf v
  | cons x xs ih =>
    intro f hf hrespect v
    exact ih _ (prescribed_embedding_load_update f t x hf hrespect.1) hrespect.2 v
end Oberwolfach
