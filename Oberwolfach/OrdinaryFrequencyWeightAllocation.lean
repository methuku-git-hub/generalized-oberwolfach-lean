module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! The retained cycle-frequency coefficients use the original per-index
ordinary marginal in the denominator. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_frequency_weight_allocation (K:ℕ) (θ c a b:ℝ) (f:Fin K→ℝ)
    (hθ0:0≤θ) (hθ1:θ≤1) (hf:∀ i,0≤f i) (hf1:∀ i,f i≤1)
    (hb:0<b) (hbalance:b=(c-1)*a+(1-θ)*∑ i,f i):
    let η:=fun i:Fin K=>(1-θ)*f i/b;
    (∀ i,0≤η i ∧ η i≤1/b) ∧ (∑ i,η i)*b+(c-1)*a=b := by
  intro η
  have hfac:0≤1-θ:=by linarith
  refine ⟨?_,?_⟩
  · intro i
    have hnum0:0≤(1-θ)*f i:=mul_nonneg hfac (hf i)
    have hnum1:(1-θ)*f i≤1:=by nlinarith [hf1 i,mul_nonneg hθ0 (hf i)]
    dsimp [η]
    exact ⟨div_nonneg hnum0 hb.le,(div_le_div_iff_of_pos_right hb).2 hnum1⟩
  · dsimp [η]
    rw [←Finset.sum_div]
    rw [div_mul_cancel₀ _ (ne_of_gt hb)]
    rw [←Finset.mul_sum]
    linarith
end Oberwolfach
