module

public import Oberwolfach.UniformExposure

@[expose] public section

/-! Concentration is preserved under independent products of exchange laws.
Each factor retains its own state space, probability law, and permitted exchanges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finiteLaw_product_exchange_mgf
    {n : ℕ} {State : Fin n → Type*} [∀ i, Fintype (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (R : ∀ i, State i → State i → Prop)
    (v : Fin n → ℝ)
    (hlaw : ∀ i (f : State i → ℝ) (b : ℝ), 0 ≤ b →
      (∀ x y, R i x y → |f x - f y| ≤ b) → ∀ u,
      (μ i).expectation (fun x => Real.exp (u * (f x - (μ i).expectation f))) ≤
        Real.exp (u ^ 2 * (v i * b ^ 2) / 8))
    (X : (∀ i, State i) → ℝ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hchange : ∀ (i : Fin n) (σ τ : ∀ j, State j),
      (∀ j, j ≠ i → σ j = τ j) → R i (σ i) (τ i) → |X σ - X τ| ≤ c i)
    (t : ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ =>
      Real.exp (t * (X σ - (FiniteLaw.pi μ).expectation X))) ≤
      Real.exp (t ^ 2 * (∑ i, v i * (c i) ^ 2) / 8) := by
  classical
  induction n with
  | zero =>
    let σ₀ : ∀ i : Fin 0, State i := fun i => Fin.elim0 i
    have hX : X = fun _ => X σ₀ := by
      funext σ
      exact congrArg X (Subsingleton.elim σ σ₀)
    rw [hX, finiteLaw_expectation_const]
    simp [finiteLaw_expectation_const]
  | succ n ih =>
    let ν := FiniteLaw.pi (fun i : Fin n => μ i.succ)
    let g (x : State 0) := ν.expectation (fun τ => X (Fin.cons x τ))
    have hmean : (FiniteLaw.pi μ).expectation X = (μ 0).expectation g :=
      finiteLaw_pi_expectation_succ μ X
    have htail (x : State 0) :
        ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) - g x))) ≤
          Real.exp (t ^ 2 * (∑ i : Fin n, v i.succ * (c i.succ) ^ 2) / 8) := by
      apply ih (fun i => μ i.succ) (fun i => R i.succ) (fun i => v i.succ)
        (fun i => hlaw i.succ) (fun τ => X (Fin.cons x τ))
        (fun i => c i.succ) (fun i => hc i.succ)
      intro i σ τ hagree hrel
      apply hchange i.succ (Fin.cons x σ) (Fin.cons x τ)
      · intro j hj
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_succ]
          exact hagree j (fun h => hj (congrArg Fin.succ h))
      · simpa only [Fin.cons_succ] using hrel
    have hedge (x y : State 0) (hrel : R 0 x y) : |g x - g y| ≤ c 0 := by
      apply finiteLaw_expectation_difference ν
      intro τ
      apply hchange 0 (Fin.cons x τ) (Fin.cons y τ)
      · intro j hj
        cases j using Fin.cases with
        | zero => exact (hj rfl).elim
        | succ j => rfl
      · simpa only [Fin.cons_zero] using hrel
    have hhead := hlaw 0 g (c 0) (hc 0) hedge t
    let A := Real.exp (t ^ 2 * (∑ i : Fin n, v i.succ * (c i.succ) ^ 2) / 8)
    have hfactor (x : State 0) :
        ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) -
          (FiniteLaw.pi μ).expectation X))) =
        Real.exp (t * (g x - (μ 0).expectation g)) *
          ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) - g x))) := by
      rw [← finiteLaw_expectation_const_mul]
      apply congrArg ν.expectation
      funext τ
      rw [← Real.exp_add, hmean]
      congr 1
      ring
    rw [finiteLaw_pi_expectation_succ]
    change (μ 0).expectation (fun x =>
      ν.expectation (fun τ => Real.exp (t * (X (Fin.cons x τ) -
        (FiniteLaw.pi μ).expectation X)))) ≤ _
    simp_rw [hfactor]
    calc
      _ ≤ (μ 0).expectation (fun x => A *
          Real.exp (t * (g x - (μ 0).expectation g))) := by
        apply finiteLaw_expectation_mono
        intro x
        have hh := mul_le_mul_of_nonneg_left (htail x)
          (Real.exp_pos (t * (g x - (μ 0).expectation g))).le
        simpa only [mul_comm] using hh
      _ = A * (μ 0).expectation (fun x =>
          Real.exp (t * (g x - (μ 0).expectation g))) :=
        finiteLaw_expectation_const_mul _ _ _
      _ ≤ A * Real.exp (t ^ 2 * (v 0 * (c 0) ^ 2) / 8) :=
        mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
      _ = _ := by
        dsimp [A]
        rw [← Real.exp_add, Fin.sum_univ_succ]
        congr 1
        ring

end Oberwolfach
