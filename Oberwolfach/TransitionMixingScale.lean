module

public import Oberwolfach.FiniteTransitionWalks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! The explicit logarithmic mixing length in the long capacity theorem. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem geometric_decay_after_logarithmic_steps (κ C ε : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 0 < C) (hε : 0 < ε)
    (hq : Real.log (C/ε) / (-Real.log (1-κ)) ≤ (q : ℝ)) :
    (1-κ)^q*C ≤ ε := by
  have hp : 0 < 1-κ := sub_pos.mpr hκ1
  have hlog : Real.log (1-κ) < 0 := Real.log_neg hp (by linarith)
  have hd : 0 < -Real.log (1-κ) := neg_pos.mpr hlog
  have hq' := (div_le_iff₀ hd).mp hq
  rw [Real.log_div hC.ne' hε.ne'] at hq'
  apply (Real.log_le_log_iff (mul_pos (pow_pos hp _) hC) hε).mp
  rw [Real.log_mul (pow_ne_zero _ hp.ne') hC.ne',Real.log_pow]
  nlinarith

theorem long_capacity_mixing_steps (κ B : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hB : 1 ≤ B) :
    (1-κ)^(⌈Real.log (10*(B+1)) / (-Real.log (1-κ))⌉₊)*(B+1) ≤ 1/10 := by
  apply geometric_decay_after_logarithmic_steps κ (B+1) (1/10) _ hκ hκ1 (by linarith) (by norm_num)
  convert Nat.le_ceil (Real.log (10*(B+1)) / (-Real.log (1-κ))) using 1
  congr 2 <;> ring

theorem relative_error_mono {X : Type*} (μ π : X → ℝ) (a b : ℝ)
    (hπ : ∀ x, 0 ≤ π x) (hab : a ≤ b) (he : RelativeError μ π a) :
    RelativeError μ π b := fun x => (he x).trans (mul_le_mul_of_nonneg_right hab (hπ x))

theorem transition_segment_mixing {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i)) (hπ0 : ∀ i x, 0 ≤ π i x)
    (hπsum : ∀ i, ∑ x, π i x = 1)
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1))
    (i L q : ℕ) (κ B ε : ℝ) (hB : 0 ≤ B) (hL : 1+q*3 ≤ L)
    (hupper : ∀ x y, R i x y ≤ B*π (i+1) y)
    (hminor : ∀ j < q, ∀ x y, κ*π (i+1+(j+1)*3) y ≤ transitionWalk R (i+1+j*3) 3 x y)
    (hdecay : (1-κ)^q*(B+1) ≤ ε) :
    ∀ x, RelativeError (transitionWalk R i L x) (π (i+L)) ε := by
  intro x
  have hinit := transition_initial_relative_error (R i x) (π (i+1)) B hB
    ((hR i).1 x) (hπ0 (i+1)) (hupper x)
  have hcontract := relative_error_block_contraction R π hR hπsum hπ (R i x)
    ((hR i).2 x) (i+1) 3 q κ (B+1) hinit hminor
  have hrow : transitionApply (R i x) (transitionWalk R (i+1) (q*3)) =
      transitionWalk R i (1+q*3) x := by
    rw [transitionWalk_add,transitionWalk_one]
    rfl
  rw [hrow] at hcontract
  have hcontract' : RelativeError (transitionWalk R i (1+q*3) x) (π (i+(1+q*3))) ε := by
    convert relative_error_mono _ _ _ _ (hπ0 _) hdecay hcontract using 1 <;> congr 1 <;> omega
  have htail := relative_error_propagated_walk R π hR hπ (i+(1+q*3)) (L-(1+q*3))
    (transitionWalk R i (1+q*3) x) ε hcontract'
  have hcompose : transitionApply (transitionWalk R i (1+q*3) x)
      (transitionWalk R (i+(1+q*3)) (L-(1+q*3))) = transitionWalk R i L x := by
    change transitionCompose _ _ x = _
    rw [← transitionWalk_add, Nat.add_sub_of_le hL]
  rw [hcompose] at htail
  convert htail using 1 <;> congr 1 <;> omega

theorem mixed_block_with_prefix_suffix {W X Y Z : Type*}
    [Fintype X] [Fintype Y]
    (A : W → X → ℝ) (R : X → Y → ℝ) (S : Y → Z → ℝ)
    (π : Y → ℝ) (ε : ℝ) (hA : IsTransition A) (hS : ∀ y z, 0 ≤ S y z)
    (hR : ∀ x, RelativeError (R x) π ε) :
    ∀ w, RelativeError (transitionCompose (transitionCompose A R) S w) (transitionApply π S) ε := by
  intro w
  exact relative_error_preserved _ _ _ _ hS
    (relative_error_averaged_rows (A w) R π ε (hA.1 w) (hA.2 w) hR)

end Oberwolfach
