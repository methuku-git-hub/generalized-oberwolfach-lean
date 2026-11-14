module

public import Oberwolfach.OrdinaryCyclePairCount
public import Oberwolfach.OrdinaryCycleIncidence

@[expose] public section
/-! A uniform upper bound on the total fixed cycle weight through two
vertices, including pairs that are not edges of the graph. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_pair_weight_bound {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (u v:V) (huv:u≠v)
    (hn:0<Fintype.card V) (B:ℝ) (hB:0≤B)
    (w:OrdinaryCycle G r→ℝ)
    (hw:∀ C,w C≤B/(Fintype.card V:ℝ)^(r-2)):
    (∑ C:OrdinaryCycle G r,
      if u∈C.val.val.support ∧ v∈C.val.val.support then w C else 0)≤(r:ℝ)^2*B := by
  let b:=B/(Fintype.card V:ℝ)^(r-2)
  have hb:0≤b:=by dsimp [b];positivity
  have hn0:(Fintype.card V:ℝ)^(r-2)≠0:=by exact ne_of_gt (pow_pos (by exact_mod_cast hn) _)
  have hcount:
    (∑ C:OrdinaryCycle G r,
      if u∈C.val.val.support ∧ v∈C.val.val.support then (1:ℝ) else 0)≤
        (r:ℝ)^2*(Fintype.card V:ℝ)^(r-2) := by
    apply (finite_subtype_sum_le (fun C:EmbeddedCycleFamily V r=>C.val≤G)
      (fun C=>if u∈C.val.support ∧ v∈C.val.support then (1:ℝ) else 0)
      (fun C=>by split_ifs <;> norm_num)).trans
    simpa only [embedded_cycle_support_range] using ordinary_cycle_two_vertex_count r u v huv
  calc
    _ ≤ ∑ C:OrdinaryCycle G r,
      (if u∈C.val.val.support ∧ v∈C.val.val.support then (1:ℝ) else 0)*b := by
        apply Finset.sum_le_sum
        intro C _
        by_cases h:u∈C.val.val.support ∧ v∈C.val.val.support
        · simpa [h,b] using hw C
        · simp [h]
    _ = (∑ C:OrdinaryCycle G r,
      if u∈C.val.val.support ∧ v∈C.val.val.support then (1:ℝ) else 0)*b := by rw [Finset.sum_mul]
    _ ≤ ((r:ℝ)^2*(Fintype.card V:ℝ)^(r-2))*b:=mul_le_mul_of_nonneg_right hcount hb
    _ = (r:ℝ)^2*B:=by dsimp [b];field_simp
end Oberwolfach
