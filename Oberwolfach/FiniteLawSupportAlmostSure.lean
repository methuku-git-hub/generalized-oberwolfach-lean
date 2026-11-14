module

public import Oberwolfach.FiniteLawSupport

@[expose] public section
/-! An event holding at every positive-mass point has probability one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_one_of_positive_mass {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (A:Ω→Prop) (h:∀ω,0<μ.mass ω→A ω):
    μ.probability A=1:=by
  rw [←finiteLaw_support_probability μ A]
  unfold FiniteLaw.probability
  calc
    _ = ∑ω,μ.support.mass ω := by
      apply Finset.sum_congr rfl
      intro ω _
      simp only [h ω.val ω.property, ite_true]
    _ = 1 := μ.support.total
end Oberwolfach
