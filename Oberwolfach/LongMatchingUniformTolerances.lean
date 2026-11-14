module

public import Oberwolfach.LongMatchingToleranceChoices

@[expose] public section
/-! Uniform bounds for smaller error tolerances, chosen before the order. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_matching_uniform_tolerances_exist
    (K:ℕ) (hK:0<K) (θ η C:ℝ) (hθ:0<θ) (hη:0<η) (hC:0≤C):
    ∃t₀ τ₀ Δ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/2 ∧ 0<Δ ∧
      ∀t τ x:ℝ,t≤t₀ → τ≤τ₀ → x≤Δ →
        ((K:ℝ)+1)*(t+C*x)+τ≤η ∧ t+C*x≤θ/(800*(K:ℝ)) :=by
  let η':=min η (1/2:ℝ)
  have hη':0<η':=lt_min hη (by norm_num)
  obtain ⟨t₀,τ₀,Δ,ht,hτ,hΔ,h⟩:=long_matching_tolerances_exist K hK θ η' C hθ hη' hC
  have hτle:τ₀≤1/2:=by
    have hh:=(h 0 (le_of_lt hΔ)).1
    have hk:0≤(K:ℝ)+1:=by positivity
    have hm:0≤((K:ℝ)+1)*t₀:=mul_nonneg hk ht.le
    have hη'half:η'≤1/2:=min_le_right _ _
    simp only [mul_zero,add_zero] at hh
    linarith
  refine ⟨t₀,τ₀,Δ,ht,hτ,hτle,hΔ,?_⟩
  intro t τ x htt hττ hx
  obtain ⟨h₁,h₂⟩:=h x hx
  have hk:0≤(K:ℝ)+1:=by positivity
  have hm:=mul_le_mul_of_nonneg_left (show t+C*x≤t₀+C*x by linarith) hk
  have hη'η:η'≤η:=min_le_left _ _
  constructor <;> linarith
end Oberwolfach
