module

public import Oberwolfach.LongOriginalRegularJointWeights

@[expose] public section
/-! On an exact regular host, the finite seed-family vertex and edge
budgets follow from any fixed positive tolerance for sufficiently large n. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority:=100000) longOriginalHostBudgetsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_original_host_seed_budgets
    (K d:ℕ) (BO:Fin K→ℝ) (hBO:∀i,0<BO i) (τ:ℝ) (hτ:0<τ):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀D:ℝ,(n:ℝ)/2≤D→
      (∀i:Fin K,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+0*(n:ℝ)≤τ*D) ∧
      (∀i:Fin K,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/(n:ℝ)≤τ):=by
  let term:=fun i:Fin K=>((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))
  let C:ℝ:=∑i:Fin K,6*term i
  have hterm:∀i,0≤term i:=by intro i;dsimp [term];have hh:=hBO i;positivity
  have hC:0≤C:=by dsimp [C];exact Finset.sum_nonneg (by intro i hi;exact mul_nonneg (by norm_num) (hterm i))
  obtain ⟨N,hN⟩:=exists_nat_gt (2*C/τ)
  refine ⟨max 1 N,by omega,?_⟩
  intro n hn D hD
  have hnN:(N:ℝ)≤n:=by exact_mod_cast (show N≤n by omega)
  have hnpos:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hCsmall:2*C≤τ*n:=by
    have hh:=mul_le_mul_of_nonneg_right (hN.le.trans hnN) hτ.le
    have he:(2*C/τ)*τ=2*C:=div_mul_cancel₀ _ hτ.ne'
    rw [he] at hh
    nlinarith only [hh]
  have hCD:C≤τ*D:=by
    have hh:=mul_le_mul_of_nonneg_left hD hτ.le
    nlinarith only [hh,hCsmall]
  constructor
  · intro i
    have hi:6*term i≤C:=by
      dsimp [C]
      exact Finset.single_le_sum (f:=fun j:Fin K=>(6:ℝ)*term j)
        (by intro j hj;exact mul_nonneg (by norm_num) (hterm j)) (Finset.mem_univ i)
    dsimp [term] at hi
    simpa only [zero_mul,add_zero] using (show 6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))≤τ*D by nlinarith only [hi,hCD])
  · intro i
    have hi:6*term i≤C:=by
      dsimp [C]
      exact Finset.single_le_sum (f:=fun j:Fin K=>(6:ℝ)*term j)
        (by intro j hj;exact mul_nonneg (by norm_num) (hterm j)) (Finset.mem_univ i)
    have h5:5*term i≤C:=by nlinarith only [hi,hterm i]
    have hh:5*term i≤τ*n:=by linarith only [h5,hCsmall,hC]
    apply (div_le_iff₀ hnpos).2
    dsimp only [term] at hh
    nlinarith only [hh]
end Oberwolfach
