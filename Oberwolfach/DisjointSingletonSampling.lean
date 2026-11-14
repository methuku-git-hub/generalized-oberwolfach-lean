module

public import Oberwolfach.DisjointPatternSampling

@[expose] public section

/-! Uniform-scale concentration for injectively indexed single physical
coordinates, including an empty tested set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_false
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : μ.probability (fun _ => False) = 0 := by
  simp [FiniteLaw.probability]

theorem finiteLaw_singleton_patterns_tail_at_scale
    {E I : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (C : Finset I) (e : I → E)
    (s : I → ∀ j, State j) (hinj : Set.InjOn e C)
    {n t : ℝ} (hcard : (C.card : ℝ) ≤ n) (ht : 0 ≤ t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t ≤ |(∑ i ∈ C, patternValue {e i} (s i) σ) - ∑ i ∈ C, (μ (e i)).mass (s i (e i))|) ≤
      2 * Real.exp (-2 * t ^ 2 / n) := by
  classical
  by_cases hC : C = ∅
  · subst C
    by_cases ht0 : t = 0
    · subst t
      norm_num [FiniteLaw.probability, (FiniteLaw.pi μ).total]
    · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      simp only [Finset.sum_empty, sub_self, abs_zero, not_le.mpr htp]
      rw [finiteLaw_probability_false]
      positivity
  · have hd : ∀ i ∈ C, ∀ j ∈ C, i ≠ j →
        Disjoint ({e i} : Finset E) {e j} := by
      intro i hi j hj hij
      simp only [Finset.disjoint_singleton_left, Finset.mem_singleton]
      exact fun he => hij (hinj hi hj he)
    have hh := finiteLaw_disjoint_patterns_tail μ C (fun i => {e i}) s hd ht
    simp only [Finset.prod_singleton, Finset.card_singleton, Nat.cast_one,
      Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC)
    have hdiv := div_le_div_of_nonneg_left (show 0 ≤ (2 : ℝ) * t ^ 2 by positivity) hpos hcard
    simpa only [neg_div, neg_mul] using neg_le_neg hdiv

end Oberwolfach
