module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Concentration for patterns with disjoint sets of physical coordinates. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def FiniteLaw.fairCoin : FiniteLaw Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

theorem disjointPattern_influence_squares
    {E I : Type*} [Fintype E] [DecidableEq E]
    (C : Finset I) (F : I → Finset E)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (F i) (F j)) :
    (∑ e : E, (∑ i ∈ C, if e ∈ F i then (1 : ℝ) else 0) ^ 2) =
      ∑ i ∈ C, ((F i).card : ℝ) := by
  classical
  have hsmall (e : E) : (C.filter (fun i => e ∈ F i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp
      (hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hsum (e : E) : (∑ i ∈ C, if e ∈ F i then (1 : ℝ) else 0) =
      ((C.filter (fun i => e ∈ F i)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hsq (e : E) : (∑ i ∈ C, if e ∈ F i then (1 : ℝ) else 0) ^ 2 =
      ∑ i ∈ C, if e ∈ F i then (1 : ℝ) else 0 := by
    simp_rw [hsum]
    have hh := hsmall e
    have he : (C.filter (fun i => e ∈ F i)).card = 0 ∨
        (C.filter (fun i => e ∈ F i)).card = 1 := by omega
    rcases he with he | he <;> simp [he]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem finiteLaw_disjoint_patterns_tail
    {E I : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e))
    (C : Finset I) (F : I → Finset E) (s : I → ∀ e, State e)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (F i) (F j))
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t ≤ |(∑ i ∈ C, patternValue (F i) (s i) σ) -
        (∑ i ∈ C, ∏ e ∈ F i, (μ e).mass (s i e))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ i ∈ C, ((F i).card : ℝ))) := by
  classical
  have hh := finiteLaw_omitted_weighted_tail μ C F ∅ s (fun _ => 1)
    (fun e => ∑ i ∈ C, if e ∈ F i then (1 : ℝ) else 0)
    (fun _ _ => zero_le_one) (fun _ => by simp) ht
  simpa only [Finset.sdiff_empty, one_mul, disjointPattern_influence_squares C F hdisj] using hh

theorem finiteLaw_fair_disjoint_patterns_tail
    {E I : Type*} [Fintype E] [DecidableEq E]
    (C : Finset I) (F : I → Finset E) (s : I → E → Bool) (k : ℕ)
    (hsize : ∀ i ∈ C, (F i).card = k)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (F i) (F j))
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : E => FiniteLaw.fairCoin)).probability (fun σ =>
      t ≤ |(∑ i ∈ C, patternValue (F i) (s i) σ) -
        (C.card : ℝ) * (1 / 2 : ℝ) ^ k|) ≤
      2 * Real.exp (-2 * t ^ 2 / ((C.card : ℝ) * k)) := by
  have hh := finiteLaw_disjoint_patterns_tail
    (fun _ : E => FiniteLaw.fairCoin) C F s hdisj ht
  have hm : (∑ i ∈ C, ∏ e ∈ F i, (FiniteLaw.fairCoin).mass (s i e)) =
      (C.card : ℝ) * (1 / 2 : ℝ) ^ k := by
    simp only [FiniteLaw.fairCoin, Finset.prod_const]
    simp only [Finset.sum_congr rfl (fun i hi => congrArg (fun j => (1 / 2 : ℝ) ^ j) (hsize i hi)),
      Finset.sum_const, nsmul_eq_mul]
  have hv : (∑ i ∈ C, ((F i).card : ℝ)) = (C.card : ℝ) * k := by
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun j : ℕ => (j : ℝ)) (hsize i hi))]
    simp
  simpa only [hm, hv] using hh

end Oberwolfach
