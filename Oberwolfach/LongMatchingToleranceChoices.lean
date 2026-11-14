module

public import Oberwolfach.LongRawMatchingAllIncidences

@[expose] public section
/-! Fixed tolerances for the matching and retained-test mass margins.
They are chosen after the matching tolerance and before the order or sample. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_matching_tolerances_exist
    (K:ℕ) (hK:0<K) (θ η C:ℝ) (hθ:0<θ) (hη:0<η) (hC:0≤C):
    ∃t τ Δ:ℝ,0<t ∧ 0<τ ∧ 0<Δ ∧
      ∀x:ℝ,x≤Δ →
        ((K:ℝ)+1)*(t+C*x)+τ≤η ∧ t+C*x≤θ/(800*(K:ℝ)) :=by
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  let r:ℝ:=min (η/(8*((K:ℝ)+1))) (θ/(1600*(K:ℝ)))
  have hr:0<r:=by dsimp [r]; positivity
  have hrη:r≤η/(8*((K:ℝ)+1)):=min_le_left _ _
  have hrθ:r≤θ/(1600*(K:ℝ)):=min_le_right _ _
  have hden:0<8*((K:ℝ)+1):=by positivity
  have hηbound:8*((K:ℝ)+1)*r≤η:=by simpa only [mul_comm] using (le_div_iff₀ hden).mp hrη
  have hθden:0<1600*(K:ℝ):=by positivity
  have hθbound:1600*(K:ℝ)*r≤θ:=by simpa only [mul_comm] using (le_div_iff₀ hθden).mp hrθ
  refine ⟨r,η/4,r/(C+1),hr,by positivity,by positivity,?_⟩
  intro x hx
  have hC1:0<C+1:=by linarith
  have hCx:C*x≤r:=by
    have hh:=mul_le_mul_of_nonneg_left hx hC
    have hfrac:C*(r/(C+1))≤r:=by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hC1).2
      nlinarith
    exact hh.trans hfrac
  constructor
  · have hKnonneg:0≤(K:ℝ)+1:=by positivity
    nlinarith [mul_nonneg hKnonneg (sub_nonneg.mpr hCx)]
  · apply (le_div_iff₀ (by positivity : 0<800*(K:ℝ))).mpr
    nlinarith [mul_nonneg hK'.le (sub_nonneg.mpr hCx)]
end Oberwolfach
