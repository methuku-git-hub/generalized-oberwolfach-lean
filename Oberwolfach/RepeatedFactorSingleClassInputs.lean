module

public import Oberwolfach.RepeatedFactorDensityOne

@[expose] public section
/-! The density-one repeated family is a single class of density one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem repeated_factor_single_class_inputs (D:ℕ) (hD:0<D) (hEven:Even D):
    let density:Unit→ℝ:=fun _=>1;
    (∀j,0≤density j) ∧ (∑j,density j)=1 ∧
    (∀j,density j=0 ∨ 1≤density j) ∧ 1≤density () ∧
    initialIndexDensity (Fin (D/2)) D=density () :=by
  dsimp only []
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j; norm_num
  · simp
  · intro j; exact Or.inr (le_refl _)
  · exact le_refl _
  · exact repeated_factor_density_one D hD hEven
end Oberwolfach
