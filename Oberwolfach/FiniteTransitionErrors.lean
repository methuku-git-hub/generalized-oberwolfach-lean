module

public import Mathlib.Tactic

@[expose] public section

/-! Relative error for finite transition matrices. The contraction estimate
uses the zero total mass of the difference of the two distributions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def transitionApply {X Y : Type*} [Fintype X]
    (μ : X → ℝ) (R : X → Y → ℝ) (y : Y) : ℝ := ∑ x, μ x * R x y

def transitionCompose {X Y Z : Type*} [Fintype Y]
    (R : X → Y → ℝ) (Q : Y → Z → ℝ) (x : X) (z : Z) : ℝ :=
  ∑ y, R x y * Q y z

def IsTransition {X Y : Type*} [Fintype Y] (R : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ R x y) ∧ ∀ x, ∑ y, R x y = 1

def RelativeError {X : Type*} (μ π : X → ℝ) (h : ℝ) : Prop :=
  ∀ x, |μ x - π x| ≤ h * π x

theorem transitionApply_sub {X Y : Type*} [Fintype X]
    (μ π : X → ℝ) (R : X → Y → ℝ) (y : Y) :
    transitionApply μ R y - transitionApply π R y =
      ∑ x, (μ x - π x) * R x y := by
  simp only [transitionApply, sub_mul, Finset.sum_sub_distrib]

theorem relative_error_preserved {X Y : Type*} [Fintype X]
    (μ π : X → ℝ) (R : X → Y → ℝ) (h : ℝ)
    (hR : ∀ x y, 0 ≤ R x y) (herror : RelativeError μ π h) :
    RelativeError (transitionApply μ R) (transitionApply π R) h := by
  intro y
  rw [transitionApply_sub]
  calc
    |∑ x, (μ x-π x)*R x y| ≤ ∑ x, |(μ x-π x)*R x y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |μ x-π x| *R x y := by simp_rw [abs_mul, abs_of_nonneg (hR _ _)]
    _ ≤ ∑ x, (h*π x)*R x y := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (herror x) (hR x y)
    _ = h * transitionApply π R y := by simp [transitionApply, Finset.mul_sum, mul_assoc]

theorem relative_error_contracted {X Y : Type*} [Fintype X]
    (μ π : X → ℝ) (R : X → Y → ℝ) (κ h : ℝ)
    (hμ : ∑ x, μ x = 1) (hπ : ∑ x, π x = 1)
    (hminor : ∀ x y, κ * transitionApply π R y ≤ R x y)
    (herror : RelativeError μ π h) :
    RelativeError (transitionApply μ R) (transitionApply π R) ((1-κ)*h) := by
  intro y
  let ν := transitionApply π R
  have hzero : ∑ x, (μ x-π x) = 0 := by rw [Finset.sum_sub_distrib,hμ,hπ,sub_self]
  have hrewrite : transitionApply μ R y - ν y =
      ∑ x, (μ x-π x)*(R x y-κ*ν y) := by
    rw [transitionApply_sub]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
  have hmass : (∑ x, π x*(R x y-κ*ν y)) = (1-κ)*ν y := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ, one_mul]
    change ν y-κ*ν y=(1-κ)*ν y
    ring
  change |transitionApply μ R y-ν y| ≤ ((1-κ)*h)*ν y
  rw [hrewrite]
  calc
    |∑ x, (μ x-π x)*(R x y-κ*ν y)| ≤ ∑ x, |(μ x-π x)*(R x y-κ*ν y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |μ x-π x| *(R x y-κ*ν y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hminor x y))]
    _ ≤ ∑ x, (h*π x)*(R x y-κ*ν y) := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (herror x) (sub_nonneg.mpr (hminor x y))
    _ = h * ((1-κ)*ν y) := by simp_rw [mul_assoc]; rw [← Finset.mul_sum,hmass]
    _ = ((1-κ)*h)*ν y := by ring

theorem transition_initial_relative_error {X : Type*}
    (μ π : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hμ : ∀ x, 0 ≤ μ x) (hπ : ∀ x, 0 ≤ π x) (hupper : ∀ x, μ x ≤ B*π x) :
    RelativeError μ π (B+1) := by
  intro x
  rw [abs_le]
  constructor <;> nlinarith [hμ x,hπ x,hupper x,mul_nonneg hB (hπ x)]

theorem transitionApply_total {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : X → ℝ) (R : X → Y → ℝ) (hR : IsTransition R) :
    (∑ y, transitionApply μ R y) = ∑ x, μ x := by
  unfold transitionApply
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hR.2,mul_one]

theorem transitionApply_compose {X Y Z : Type*} [Fintype X] [Fintype Y]
    (μ : X → ℝ) (R : X → Y → ℝ) (Q : Y → Z → ℝ) :
    transitionApply (transitionApply μ R) Q = transitionApply μ (transitionCompose R Q) := by
  funext z
  simp only [transitionApply,transitionCompose,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem transitionCompose_isTransition {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (R : X → Y → ℝ) (Q : Y → Z → ℝ) (hR : IsTransition R) (hQ : IsTransition Q) :
    IsTransition (transitionCompose R Q) := by
  constructor
  · intro x z
    exact Finset.sum_nonneg fun y _ => mul_nonneg (hR.1 x y) (hQ.1 y z)
  · intro x
    exact (transitionApply_total (R x) Q hQ).trans (hR.2 x)

theorem transitionCompose_assoc {W X Y Z : Type*} [Fintype X] [Fintype Y]
    (P : W → X → ℝ) (R : X → Y → ℝ) (Q : Y → Z → ℝ) :
    transitionCompose (transitionCompose P R) Q = transitionCompose P (transitionCompose R Q) := by
  funext w z
  exact congrFun (transitionApply_compose (P w) R Q) z

theorem relative_error_averaged_rows {X Y : Type*} [Fintype X]
    (μ : X → ℝ) (R : X → Y → ℝ) (π : Y → ℝ) (h : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hs : ∑ x, μ x = 1)
    (hrow : ∀ x, RelativeError (R x) π h) : RelativeError (transitionApply μ R) π h := by
  intro y
  have heq : transitionApply μ R y-π y = ∑ x, μ x*(R x y-π y) := by
    simp [transitionApply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
  rw [heq]
  calc
    |∑ x, μ x*(R x y-π y)| ≤ ∑ x, |μ x*(R x y-π y)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, μ x*|R x y-π y| := by simp_rw [abs_mul, abs_of_nonneg (hμ _)]
    _ ≤ ∑ x, μ x*(h*π y) := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hrow x y) (hμ x)
    _ = h*π y := by rw [← Finset.sum_mul,hs,one_mul]

end Oberwolfach
