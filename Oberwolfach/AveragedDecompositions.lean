module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Averaging exact finite decomposition weights preserves the exact
incidence equations. The normalizing probability is fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def averagedWeight {Ω T : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) (ρ : ℝ) (t : T) : ℝ :=
  μ.expectation (fun ω => w ω t) / ρ

theorem averagedWeight_nonneg {Ω T : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ ω t, 0 ≤ w ω t) (t : T) : 0 ≤ averagedWeight μ w ρ t := by
  apply div_nonneg _ hρ
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hw ω t))

theorem averagedWeight_incidence {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) (ρ : ℝ) (I : T → Prop) :
    (∑ t, if I t then averagedWeight μ w ρ t else 0) =
      μ.expectation (fun ω => ∑ t, if I t then w ω t else 0) / ρ := by
  unfold averagedWeight FiniteLaw.expectation
  have hterm (t : T) : (if I t then (∑ ω, μ.mass ω * w ω t) / ρ else 0) =
      (∑ ω, μ.mass ω * (if I t then w ω t else 0)) / ρ := by
    by_cases hi : I t <;> simp [hi]
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem averagedWeight_exact_load {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) (ρ : ℝ)
    (I : T → Prop) (A : Ω → Prop) (k : ℝ)
    (hload : ∀ ω, (∑ t, if I t then w ω t else 0) = if A ω then k else 0) :
    (∑ t, if I t then averagedWeight μ w ρ t else 0) = k * μ.probability A / ρ := by
  rw [averagedWeight_incidence]
  simp_rw [hload]
  unfold FiniteLaw.expectation FiniteLaw.probability
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : A ω <;> simp [h, mul_comm]

theorem averagedWeight_load_interval {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) {ρ δ : ℝ} (hρ : 0 < ρ)
    (I : T → Prop) (A : Ω → Prop)
    (hload : ∀ ω, (∑ t, if I t then w ω t else 0) = if A ω then 1 else 0)
    (hp : (1 - δ) * ρ ≤ μ.probability A ∧ μ.probability A ≤ ρ) :
    1 - δ ≤ (∑ t, if I t then averagedWeight μ w ρ t else 0) ∧
      (∑ t, if I t then averagedWeight μ w ρ t else 0) ≤ 1 := by
  rw [averagedWeight_exact_load μ w ρ I A 1 hload, one_mul]
  exact ⟨(le_div_iff₀ hρ).mpr hp.1, (div_le_one hρ).mpr hp.2⟩

theorem averagedWeight_pointwise_bounds {Ω T : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) {ρ a C : ℝ} (hρ : 0 < ρ)
    (S : Ω → T → Prop) (hw : ∀ ω t, 0 ≤ w ω t)
    (hlo : ∀ ω t, S ω t → a ≤ w ω t) (hhi : ∀ ω t, w ω t ≤ C) (t : T) :
    a * μ.probability (fun ω => S ω t) / ρ ≤ averagedWeight μ w ρ t ∧
      averagedWeight μ w ρ t ≤ C / ρ := by
  have hlow := finiteLaw_expectation_mono μ
    (fun ω => if S ω t then a else 0) (fun ω => w ω t)
    (by intro ω; split_ifs with h; exact hlo ω t h; exact hw ω t)
  have hhigh := finiteLaw_expectation_mono μ (fun ω => w ω t) (fun _ => C)
    (fun ω => hhi ω t)
  rw [finiteLaw_expectation_const] at hhigh
  have hex : μ.expectation (fun ω => if S ω t then a else 0) =
      a * μ.probability (fun ω => S ω t) := by
    unfold FiniteLaw.expectation FiniteLaw.probability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : S ω t <;> simp [h, mul_comm]
  rw [hex] at hlow
  exact ⟨div_le_div_of_nonneg_right hlow hρ.le,
    div_le_div_of_nonneg_right hhigh hρ.le⟩

end Oberwolfach
