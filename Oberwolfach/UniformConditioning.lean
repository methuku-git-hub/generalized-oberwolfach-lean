module

public import Oberwolfach.SubsetCounts

@[expose] public section

/-! Conditioning a uniform finite law on a nonempty event gives the
uniform law on that event. The event remains a fixed subset of the
original sample space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def intersectionSubtypeEquiv {Ω : Type*} (E A : Ω → Prop) :
    {ω // E ω ∧ A ω} ≃ {ω : {ω // E ω} // A ω.1} where
  toFun ω := ⟨⟨ω.1, ω.2.1⟩, ω.2.2⟩
  invFun ω := ⟨ω.1.1, ω.1.2, ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniform_probability_intersection {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E A : Ω → Prop) [F : Fintype {ω // E ω}] [Nonempty {ω // E ω}] :
    (FiniteLaw.uniform Ω).probability (fun ω => E ω ∧ A ω) =
      (FiniteLaw.uniform Ω).probability E *
        (FiniteLaw.uniform {ω // E ω}).probability (fun ω => A ω.1) := by
  have hF : F = @Subtype.fintype Ω E (fun _ => Classical.propDecidable _) inferInstance :=
    Subsingleton.elim _ _
  cases hF
  rw [finiteLaw_uniform_probability, finiteLaw_uniform_probability,
    finiteLaw_uniform_probability]
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card {ω // E ω} : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  norm_cast
  convert! Fintype.card_congr (intersectionSubtypeEquiv E A) using 1
  congr 1
  exact Subsingleton.elim _ _

end Oberwolfach
