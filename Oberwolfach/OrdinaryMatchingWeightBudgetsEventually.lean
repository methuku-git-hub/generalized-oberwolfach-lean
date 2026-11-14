module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Finite, fixed seed constants fit the matching normalization budgets for
large order whenever the regular host has at least half the vertices in each
degree. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_weight_budgets_eventually
    (K d:ℕ) (B:Fin K→ℝ) (τ:ℝ) (hτ:0<τ):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀D:ℝ,(n:ℝ)/2≤D→
    (∀i:Fin K,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+(τ/4)*(n:ℝ)≤τ*D) ∧
    (∀i:Fin K,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))/(n:ℝ)≤τ) :=by
  let A:Fin K→ℝ:=fun i=>6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))
  let C:Fin K→ℝ:=fun i=>5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))
  let T:ℝ:=∑i:Fin K,(|A i|+|C i|)
  obtain ⟨N,hN⟩:=ordinary_constant_eventually_below_linear_rate (τ/4) T (by positivity)
  refine ⟨N,?_⟩
  intro n hn hn0 D hD
  have hnR:0<(n:ℝ):=by exact_mod_cast hn0
  have hT:=hN n hn
  have hbound:∀i:Fin K,|A i|+|C i|≤T:=by
    intro i
    dsimp [T]
    exact Finset.single_le_sum (s:=Finset.univ) (f:=fun j:Fin K=>|A j|+|C j|)
      (fun j _=>add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  constructor
  · intro i
    have hi:=hbound i
    have ha:=le_abs_self (A i)
    dsimp [A] at *
    nlinarith [abs_nonneg (C i),mul_le_mul_of_nonneg_left hD hτ.le]
  · intro i
    apply (div_le_iff₀ hnR).2
    have hi:=hbound i
    have hc:=le_abs_self (C i)
    dsimp [C] at *
    nlinarith [abs_nonneg (A i)]
end Oberwolfach
