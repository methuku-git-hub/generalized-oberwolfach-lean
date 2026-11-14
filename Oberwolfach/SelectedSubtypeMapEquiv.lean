module

public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Basic

@[expose] public section
/-! A selected subfamily survives an injective change of ambient resource type. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {A B : Type} [DecidableEq A] [DecidableEq B]

def selectedSubtypeMapEquiv (e : A ↪ B) (M : Finset A) (P : A → Prop) (Q : B → Prop)
    (hPQ : ∀ a, Q (e a) ↔ P a) :
    {a : A // a ∈ M ∧ P a} ≃ {b : B // b ∈ M.map e ∧ Q b} := by
  classical
  apply Equiv.ofBijective (fun a => ⟨e a.val, Finset.mem_map.mpr ⟨a.val, a.property.1, rfl⟩,
    (hPQ a.val).2 a.property.2⟩)
  constructor
  · intro x y h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  · intro y
    obtain ⟨a, ha, hay⟩ := Finset.mem_map.mp y.property.1
    have hp : P a := (hPQ a).1 (by simpa [hay] using y.property.2)
    refine ⟨⟨a, ha, hp⟩, ?_⟩
    exact Subtype.ext hay
end Oberwolfach
