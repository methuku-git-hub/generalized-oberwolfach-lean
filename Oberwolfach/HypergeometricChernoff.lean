module

public import Oberwolfach.HypergeometricPower
public import Oberwolfach.SubsetMean
public import Oberwolfach.FiniteChernoff

@[expose] public section

/-! Multiplicative Chernoff estimates for the actual uniform fixed-size subset law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_intersection_mgf {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (A : Finset V) (s : ℝ) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => Real.exp (s * ((A ∩ S.1).card : ℝ))) ≤
      Real.exp (((A.card : ℝ) * ((r : ℝ) / Fintype.card V)) * (Real.exp s - 1)) := by
  have hp : (r : ℝ) / Fintype.card V ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast hr) (by positivity)
  have hp0 : 0 ≤ (r : ℝ) / Fintype.card V := by positivity
  have hb : 0 ≤ 1 + ((r : ℝ) / Fintype.card V) * (Real.exp s - 1) := by
    nlinarith [mul_nonneg hp0 (Real.exp_pos s).le]
  have he : 1 + ((r : ℝ) / Fintype.card V) * (Real.exp s - 1) ≤
      Real.exp (((r : ℝ) / Fintype.card V) * (Real.exp s - 1)) := by
    simpa only [add_comm] using Real.add_one_le_exp
      (((r : ℝ) / Fintype.card V) * (Real.exp s - 1))
  calc
    _ = (FiniteLaw.uniform (FixedSubset V r)).expectation
        (fun S => (Real.exp s) ^ (A ∩ S.1).card) := by
      congr 1
      funext S
      rw [mul_comm, Real.exp_nat_mul]
    _ ≤ (1 + ((r : ℝ) / Fintype.card V) * (Real.exp s - 1)) ^ A.card :=
      fixedSubset_power_bound hr A (Real.exp_pos s)
    _ ≤ (Real.exp (((r : ℝ) / Fintype.card V) * (Real.exp s - 1))) ^ A.card :=
      pow_le_pow_left₀ hb he _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem fixedSubset_chernoff {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (A : Finset V)
    {ε : ℝ} (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    let a := (FiniteLaw.uniform (FixedSubset V r)).expectation (fun S => ((A ∩ S.1).card : ℝ))
    (FiniteLaw.uniform (FixedSubset V r)).probability
      (fun S => ε * a ≤ |((A ∩ S.1).card : ℝ) - a|) ≤ 2 * Real.exp (-ε ^ 2 * a / 3) := by
  dsimp only
  rw [fixedSubset_intersection_mean hr]
  exact finiteLaw_poisson_mgf_absolute_tail _ _ (by positivity)
    (fixedSubset_intersection_mgf hr A) he he1

theorem fixedSubset_chernoff_large {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (A : Finset V)
    (ha : 0 < (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => ((A ∩ S.1).card : ℝ)))
    {t : ℝ} (ht : (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => ((A ∩ S.1).card : ℝ)) ≤ t) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => t ≤ ((A ∩ S.1).card : ℝ)) ≤
      (Real.exp 1 * (FiniteLaw.uniform (FixedSubset V r)).expectation
        (fun S => ((A ∩ S.1).card : ℝ)) / t) ^ t := by
  rw [fixedSubset_intersection_mean hr] at ha ht ⊢
  exact finiteLaw_poisson_mgf_large_tail _ _ ha (fixedSubset_intersection_mgf hr A) ht

theorem fixedSubset_intersection_zero_mean {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (A : Finset V)
    (hzero : (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => ((A ∩ S.1).card : ℝ)) = 0) (S : FixedSubset V r) :
    (A ∩ S.1).card = 0 := by
  have hpos : 0 < (FiniteLaw.uniform (FixedSubset V r)).mass S := by
    change 0 < 1 / (Fintype.card (FixedSubset V r) : ℝ)
    positivity
  exact_mod_cast finiteLaw_nonnegative_zero_mean _ _ (fun _ => by positivity) hzero S hpos

end Oberwolfach
