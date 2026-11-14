module

public import Mathlib.Logic.Equiv.Basic

@[expose] public section
/-! Restrict an equivalence to a specified fiber. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {A B U : Type}

def selectedSubtypeFiberEquiv (e : A ≃ B) (f : B → U) (w : U) :
    {a : A // f (e a) = w} ≃ {b : B // f b = w} :=
  e.subtypeEquiv (fun _ => Iff.rfl)
end Oberwolfach
