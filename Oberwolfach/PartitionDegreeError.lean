module

public import Oberwolfach.GraphPartitionDegrees

@[expose] public section

/-! Explicit margins for conditioning on finitely many prescribed labels.
The resulting common-event bound retains the uniform fixed-size partition
law and its original degree centre. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem conditional_degree_tail_scale {r d m R η ε : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hd : 0 ≤ d) (hsum : r + d = m)
    (hm : 0 < m) (hη : 0 < η) (hη1 : η ≤ 1)
    (hroots : 2 * R ≤ η * m / 4) (hε : ε ≤ η / 4) :
    0 < d ∧ η * m / 2 + 2 * R + ε * m ≤ η * m ∧
      2 * Real.exp (-2 * (η * m / 2) ^ 2 / d) ≤
        2 * Real.exp (-η ^ 2 * m / 2) := by
  have hηm : η * m ≤ m := by nlinarith [mul_nonneg (sub_nonneg.mpr hη1) hm.le]
  have hdpos : 0 < d := by linarith
  have hεm := mul_le_mul_of_nonneg_right hε hm.le
  refine ⟨hdpos, by linarith, ?_⟩
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hdpos).mpr
  have hdm : d ≤ m := by linarith
  have hh := mul_le_mul_of_nonneg_left hdm (sq_nonneg η)
  have hhm := mul_le_mul_of_nonneg_right hh hm.le
  nlinarith

theorem rooted_graph_equal_cells_good {X Y J : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] [Fintype J]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (G : SimpleGraph (X ⊕ Y)) (σ : J → Equiv.Perm (X ⊕ Y))
    (classes : Finset (Fin k)) (m : ℕ) (hm : 0 < m)
    (hsize : ∀ a ∈ classes, rootCellSize r a + d a = m)
    (D ε η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : ε ≤ η / 4)
    (hroots : 2 * (Fintype.card X : ℝ) ≤ η * m / 4)
    (hdeg : ∀ v, |(G.degree v : ℝ) - D| ≤
      ε * ((Fintype.card X : ℝ) + Fintype.card Y)) :
    1 - (classes.card : ℝ) * Fintype.card J *
        (Fintype.card X + Fintype.card Y) *
          (2 * Real.exp (-η ^ 2 * m / 2)) ≤
    (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => ∀ a ∈ classes, ∀ j v,
        |(graphCellDegree G (σ j) P.1 v a : ℝ) -
          D * ((m : ℝ) / ((Fintype.card X : ℝ) + Fintype.card Y))| < η * m) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hsz (a) (ha : a ∈ classes) : (rootCellSize r a : ℝ) + d a = m := by
    exact_mod_cast hsize a ha
  have hcalc (a) (ha : a ∈ classes) := conditional_degree_tail_scale
    (show (0 : ℝ) ≤ rootCellSize r a by positivity)
    (show (rootCellSize r a : ℝ) ≤ Fintype.card X by
      exact_mod_cast Fintype.card_subtype_le (fun x => r x = a))
    (show (0 : ℝ) ≤ d a by positivity) (hsz a ha) hmr hη hη1 hroots hε
  have h := rooted_graph_degrees_common_event r d G σ classes D ε η (η * m / 2)
    (by positivity) hdeg (by
      intro a ha
      rw [hsz a ha]
      exact (hcalc a ha).2.1)
  have hs : (∑ a ∈ classes, (Fintype.card J : ℝ) *
      (Fintype.card X + Fintype.card Y) * (2 * Real.exp (-2 * (η * m / 2) ^ 2 / (d a : ℝ)))) ≤
      (classes.card : ℝ) * Fintype.card J * (Fintype.card X + Fintype.card Y) *
        (2 * Real.exp (-η ^ 2 * m / 2)) := by
    calc
      _ ≤ ∑ _a ∈ classes, (Fintype.card J : ℝ) *
          (Fintype.card X + Fintype.card Y) * (2 * Real.exp (-η ^ 2 * m / 2)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hcalc a ha).2.2 (by positivity)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  apply (sub_le_sub_left hs 1).trans
  apply h.trans_eq
  congr 1
  ext P
  constructor
  · intro hp a ha j v
    simpa only [hsz a ha] using hp a ha j v
  · intro hp a ha j v
    simpa only [hsz a ha] using hp a ha j v

end Oberwolfach
