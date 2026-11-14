module

public import Oberwolfach.ResidualPathMargin
public import Oberwolfach.IntervalPathWeights

@[expose] public section

/-! Strict positivity of every residual endpoint entry at a positive margin. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem positive_margin_base {q n δ α : ℝ} (hq : 2 ≤ q) (hn : 0 < n)
    (hα : 0 < α) (ht : (q + (2 * q - 1) * α) * n ≤ (2 * q - 1) * δ) :
    0 < δ ∧ q * n ≤ (2 * q - 1) * δ := by
  have hq0 : 0 < q := by linarith
  have hf : 0 < 2 * q - 1 := by linarith
  have hx := mul_pos (mul_pos hf hα) hn
  have hb : q * n ≤ (2 * q - 1) * δ := by nlinarith
  exact ⟨pos_of_mul_pos_right (lt_of_lt_of_le (mul_pos hq0 hn) hb) hf.le, hb⟩

theorem intervalResidualMap_pos {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (q δ α : ℝ) (hq : 2 ≤ q) (hn : 0 < Fintype.card Y) (hα : 0 < α)
    (hcard : Fintype.card X = Fintype.card Y)
    (ht : (q + (2 * q - 1) * α) * Fintype.card Y ≤ (2 * q - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hdY : ∀ y, δ ≤ (Finset.univ.filter (fun x => L x y)).card)
    (hbal : ∀ y, (Finset.univ.filter (fun x => L x y)).card =
      (Finset.univ.filter (R y)).card)
    (hQ : Q ∈ transportMatrices
      (fun x => (Finset.univ.filter (L x)).card / q)
      (fun z => (Finset.univ.filter (fun y => R y z)).card / q))
    (x : X) (z : Z) : 0 < intervalResidualMap L R q Q x z := by
  have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
  obtain ⟨hδ, hbase⟩ := positive_margin_base hq hn' hα ht
  have hc := intervalCommon_pos L R q δ hq hn hδ.le hbase hdL hdR x z
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hc
  obtain ⟨hxy, hyz⟩ := (Finset.mem_filter.mp hy).2
  have hl := (interval_residual_path_two_sided L R Q q δ α hq hn hα hcard
    ht hdL hdR hdY hQ x y z hxy hyz).1
  have hσ : 0 < (2 * q - 1) * α / q := div_pos (mul_pos (by linarith) hα) (by linarith)
  have hp : 0 < scaledResidualPath (interfaceCapacity L) (interfaceCapacity R)
      (endpointReserve L R Q) q x y z :=
    lt_of_lt_of_le (div_pos (pow_pos hσ 2) (mul_pos (by linarith) hn')) hl
  change 0 < ∑ b, scaledResidualPath (interfaceCapacity L) (interfaceCapacity R)
    (endpointReserve L R Q) q x b z
  exact lt_of_lt_of_le hp (Finset.single_le_sum
    (fun b _ => interval_scaled_path_nonneg L R q δ hq hn hδ.le hbase
      hdL hdR hbal hQ x b z) (Finset.mem_univ y))

end Oberwolfach
