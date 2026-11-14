module

public import Oberwolfach.WeightedProducts

@[expose] public section

/-!
Finite categorical sampling, including fixed root-omitted expectations and
projection of a common event. The probability of a configuration is the
product of its coordinate probabilities. No coordinate is resampled or
conditioned on the value of a designated root.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

/-- A probability law on a finite sample space, given by its point masses. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * X ω

def probability (μ : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then μ.mass ω else 0

/-- Independent product of finite laws. -/
def prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  mass ω := μ.mass ω.1 * ν.mass ω.2
  nonneg ω := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.total, mul_one]
    exact μ.total

/-- Independent categorical choices with possibly different state types
and different probability vectors at different coordinates. -/
def pi {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) : FiniteLaw (∀ e, State e) where
  mass σ := ∏ e, (μ e).mass (σ e)
  nonneg σ := Finset.prod_nonneg (fun e _ => (μ e).nonneg (σ e))
  total := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).total, Finset.prod_const_one]

end FiniteLaw
open FiniteLaw

theorem finiteLaw_expectation_pattern
    {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (F : Finset E) (s : ∀ e, State e) :
    (pi μ).expectation (patternValue F s) = ∏ e ∈ F, (μ e).mass (s e) := by
  classical
  let g (e : E) (x : State e) :=
    if e ∈ F then (μ e).mass x * (if x = s e then 1 else 0) else (μ e).mass x
  have hpoint (σ : ∀ e, State e) :
      (∏ e, (μ e).mass (σ e)) * patternValue F s σ = ∏ e, g e (σ e) := by
    have hprod : patternValue F s σ =
        ∏ e, if e ∈ F then (if σ e = s e then (1 : ℝ) else 0) else 1 := by
      unfold patternValue
      simp
    rw [hprod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e ∈ F <;> simp [g, he]
  have hsum (e : E) : ∑ x, g e x = if e ∈ F then (μ e).mass (s e) else 1 := by
    by_cases he : e ∈ F
    · simp [g, he, mul_ite]
    · simp only [g, ite_eq_right he]
      exact (μ e).total
  unfold expectation
  change (∑ σ, (∏ e, (μ e).mass (σ e)) * patternValue F s σ) = _
  simp_rw [hpoint]
  rw [← Fintype.prod_sum]
  simp_rw [hsum]
  simp

/-- Fixed candidate families and fixed coefficients may be summed after
omitting root coordinates from every product. This is an unconditional
expectation identity, not conditioning on root presence. -/
theorem finiteLaw_expectation_omitted_root_sum
    {E I : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (C : Finset I)
    (F : I → Finset E) (R : Finset E)
    (s : I → ∀ e, State e) (w : I → ℝ) :
    (pi μ).expectation (fun σ => ∑ i ∈ C, w i * patternValue (F i \ R) (s i) σ) =
      ∑ i ∈ C, w i * ∏ e ∈ F i \ R, (μ e).mass (s i e) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = w i * (pi μ).expectation (patternValue (F i \ R) (s i)) := by
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by rw [finiteLaw_expectation_pattern]

/-- A joint event implies one event in the first coordinate, uniformly
over all later admissible choices. In particular, the auxiliary random
coordinate is eliminated once for the entire family of later choices. -/
theorem finiteLaw_common_event_projection
    {Ω Γ X Y : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (E : Ω → Γ → Prop) (admissible : Ω → X → Prop)
    (conclusion : Ω → X → Y → Prop)
    (hE : ∀ ω γ, E ω γ → ∀ x, admissible ω x → ∃ y, conclusion ω x y) :
    (μ.prod ν).probability (fun z => E z.1 z.2) ≤
      μ.probability (fun ω => ∀ x, admissible ω x → ∃ y, conclusion ω x y) := by
  classical
  unfold probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hgood : ∀ x, admissible ω x → ∃ y, conclusion ω x y
  · rw [ite_eq_left hgood]
    calc
      _ ≤ ∑ γ, μ.mass ω * ν.mass γ := by
        apply Finset.sum_le_sum
        intro γ _
        change (if E ω γ then μ.mass ω * ν.mass γ else 0) ≤ _
        split_ifs
        · rfl
        · exact mul_nonneg (μ.nonneg ω) (ν.nonneg γ)
      _ = μ.mass ω := by rw [← Finset.mul_sum, ν.total, mul_one]
  · have hbad (γ : Γ) : ¬E ω γ := fun h => hgood (hE ω γ h)
    simp [hgood, hbad]

/-- One physical edge receives a categorical colour and an independent
fair direction. Both possible directions belong to this one coordinate. -/
def FiniteLaw.categoricalDirection {k : ℕ} (ρ : Fin k → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1) : FiniteLaw (Fin k × Bool) where
  mass s := ρ s.1 / 2
  nonneg s := div_nonneg (hρ s.1) (by norm_num)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro a _
    ring

/-- The indicator that a particular physical edge has colour `a` and its
chosen direction meets a fixed cut. `forward` and `reverse` record the two
endpoint tests; they are allowed to hold simultaneously. -/
def directedCutContribution {k : ℕ} (a : Fin k) (forward reverse : Prop)
    [Decidable forward] [Decidable reverse] (s : Fin k × Bool) : ℝ :=
  if s.1 = a then
    if s.2 then (if forward then 1 else 0) else (if reverse then 1 else 0)
  else 0

theorem directedCutContribution_bounds
    {k : ℕ} (a : Fin k) (forward reverse : Prop)
    [Decidable forward] [Decidable reverse] (s : Fin k × Bool) :
    directedCutContribution a forward reverse s ∈ Set.Icc (0 : ℝ) 1 := by
  unfold directedCutContribution
  split_ifs <;> norm_num

/-- If both directions of a physical edge meet a cut, its expected
contribution is `ρ a`, not two independent Bernoulli contributions. -/
theorem categoricalDirection_expected_cut
    {k : ℕ} (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (forward reverse : Prop)
    [Decidable forward] [Decidable reverse] :
    (FiniteLaw.categoricalDirection ρ hρ htotal).expectation
      (directedCutContribution a forward reverse) =
      ρ a / 2 * ((if forward then 1 else 0) + (if reverse then 1 else 0)) := by
  classical
  unfold expectation directedCutContribution
  simp only [FiniteLaw.categoricalDirection, Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases hf : forward <;> by_cases hr : reverse <;>
    (simp [hf, hr, mul_ite, Finset.sum_add_distrib] <;> ring)

end Oberwolfach
