module

public import Mathlib.Data.Real.Basic

@[expose] public section
/-! Distribute a classical conjunction test with an arbitrary outer decision instance. -/
noncomputable section
namespace Oberwolfach
theorem mixed_ite_and (P Q:Prop) (d:Decidable P) (a b:ℝ):
    @ite ℝ (P∧Q) (Classical.propDecidable _) a b =
      @ite ℝ P d (@ite ℝ Q (Classical.propDecidable _) a b) b := by
  classical
  by_cases hP:P <;> by_cases hQ:Q <;> simp [hP,hQ]
end Oberwolfach
