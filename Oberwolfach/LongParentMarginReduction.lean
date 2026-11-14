module

public import Oberwolfach.LongHostGeometryExactReferenceTrim

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_parent_margin_reduction (α:ℝ) (hα:0<α):
    ∃αHost:ℝ,0<αHost ∧ αHost≤α ∧ αHost≤1 ∧
      ∀(n:ℕ) (threshold D:ℝ),
        (threshold+α)*n≤D→(threshold+αHost)*n≤D := by
  refine ⟨min α 1,lt_min hα (by norm_num),min_le_left _ _,min_le_right _ _,?_⟩
  intro n threshold D hD
  have hcoeff:threshold+min α 1≤threshold+α:=by linarith [min_le_left α 1]
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)).trans hD
end Oberwolfach
