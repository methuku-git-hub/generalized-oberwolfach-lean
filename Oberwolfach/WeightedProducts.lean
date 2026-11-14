module

public import Mathlib.Tactic

@[expose] public section

/-! Manuscript `lem:pr:wi-stability`, with dependent coordinate state types.
Candidate sets and nonnegative weights are fixed in both evaluations. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

noncomputable def patternValue {E : Type*} {State : E → Type*}
    (F : Finset E) (s ρ : ∀ e, State e) : ℝ := by
  classical
  exact ∏ e ∈ F, if ρ e = s e then (1 : ℝ) else 0

theorem patternValue_indicator {E : Type*} {State : E → Type*}
    (F : Finset E) (s ρ : ∀ e, State e) :
    patternValue F s ρ = if ∀ e ∈ F, ρ e = s e then 1 else 0 := by
  classical
  simp [patternValue, Finset.prod_boole]

theorem patternValue_mem_unit {E : Type*} {State : E → Type*}
    (F : Finset E) (s ρ : ∀ e, State e) :
    0 ≤ patternValue F s ρ ∧ patternValue F s ρ ≤ 1 := by
  rw [patternValue_indicator]
  split_ifs <;> norm_num

theorem pattern_change_bound {E : Type*} [DecidableEq E] {State : E → Type*}
    (F D : Finset E) (s σ τ : ∀ e, State e)
    (h : ∀ e ∈ F, e ∉ D → σ e = τ e) :
    |patternValue F s τ - patternValue F s σ| ≤
      ∑ e ∈ D, if e ∈ F then (1 : ℝ) else 0 := by
  classical
  by_cases hhit : ∃ e ∈ D, e ∈ F
  · obtain ⟨e, heD, heF⟩ := hhit
    have hlo := (patternValue_mem_unit F s τ).1
    have hhi := (patternValue_mem_unit F s τ).2
    have hlo' := (patternValue_mem_unit F s σ).1
    have hhi' := (patternValue_mem_unit F s σ).2
    have hv : |patternValue F s τ - patternValue F s σ| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hs : (1 : ℝ) ≤ ∑ e ∈ D, if e ∈ F then (1 : ℝ) else 0 := by
      have ht := Finset.single_le_sum
        (s := D) (f := fun e => if e ∈ F then (1 : ℝ) else 0)
        (fun e _ => by split_ifs <;> norm_num) heD
      simpa [heF] using ht
    exact hv.trans hs
  · have heq : patternValue F s σ = patternValue F s τ := by
      unfold patternValue
      apply Finset.prod_congr rfl
      intro e he
      rw [h e he (fun heD => hhit ⟨e, heD, he⟩)]
    rw [heq, sub_self, abs_zero]
    exact Finset.sum_nonneg (fun e _ => by split_ifs <;> norm_num)

/-- Each occurrence contributes once for each candidate using it. Repeated
physical images are not identified by this inequality. -/
theorem weighted_product_stability {E I : Type*} [DecidableEq E]
    {State : E → Type*} (C : Finset I) (F : I → Finset E)
    (s : I → ∀ e, State e) (w : I → ℝ) (D : Finset E) (σ τ : ∀ e, State e)
    (hw : ∀ i ∈ C, 0 ≤ w i)
    (h : ∀ i ∈ C, ∀ e ∈ F i, e ∉ D → σ e = τ e) :
    |(∑ i ∈ C, w i * patternValue (F i) (s i) τ) -
      ∑ i ∈ C, w i * patternValue (F i) (s i) σ| ≤
    ∑ e ∈ D, ∑ i ∈ C, if e ∈ F i then w i else 0 := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ C, |w i * patternValue (F i) (s i) τ -
        w i * patternValue (F i) (s i) σ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ C, w i * |patternValue (F i) (s i) τ -
        patternValue (F i) (s i) σ| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ C, w i * (∑ e ∈ D, if e ∈ F i then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (pattern_change_bound (F i) D (s i) σ τ (h i hi))
        (hw i hi)
    _ = ∑ e ∈ D, ∑ i ∈ C, if e ∈ F i then w i else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp_all

/-- Root occurrences are removed from each product. Their states may differ
arbitrarily, and neither sample is conditioned on root presence. -/
theorem omitted_root_stability {E I : Type*} [DecidableEq E]
    {State : E → Type*} (C : Finset I) (F : I → Finset E)
    (R D : Finset E) (s : I → ∀ e, State e) (w : I → ℝ)
    (σ τ : ∀ e, State e) (hw : ∀ i ∈ C, 0 ≤ w i)
    (h : ∀ i ∈ C, ∀ e ∈ F i, e ∉ R → e ∉ D → σ e = τ e) :
    |(∑ i ∈ C, w i * patternValue (F i \ R) (s i) τ) -
      ∑ i ∈ C, w i * patternValue (F i \ R) (s i) σ| ≤
    ∑ e ∈ D, ∑ i ∈ C, if e ∈ F i \ R then w i else 0 := by
  classical
  apply weighted_product_stability C (fun i => F i \ R) s w D σ τ hw
  intro i hi e he heD
  exact h i hi e (Finset.mem_sdiff.mp he).1 (Finset.mem_sdiff.mp he).2 heD

end Oberwolfach
