module

public import Oberwolfach.LongMatchingUniformTolerances

@[expose] public section
/-! Fixed tolerances that suffice for the manuscript's sharper retained-test
mass constant, as well as the simultaneous matching load condition. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_matching_manuscript_uniform_tolerances_exist
    (K:ℕ) (hK:0<K) (θ η C:ℝ) (hθ:0<θ) (hη:0<η) (hC:0≤C):
    ∃t₀ τ₀ Δ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧
      ∀t τ x:ℝ,t≤t₀→τ≤τ₀→x≤Δ→
        ((K:ℝ)+1)*(t+C*x)+τ≤η ∧ t+C*x≤θ/(3200*(K:ℝ)) :=by
  let η':=min η (1/16:ℝ)
  have hη':0<η':=lt_min hη (by norm_num)
  obtain ⟨t₀,τ₀,Δ,ht,hτ,_,hΔ,h⟩:=
    long_matching_uniform_tolerances_exist K hK (θ/4) η' C (by positivity) hη' hC
  have hτle:τ₀≤1/16:=by
    have hh:=(h t₀ τ₀ 0 le_rfl le_rfl hΔ.le).1
    have hk:0≤(K:ℝ)+1:=by positivity
    have hm:0≤((K:ℝ)+1)*t₀:=mul_nonneg hk ht.le
    have hη'bound:η'≤1/16:=min_le_right _ _
    simp only [mul_zero,add_zero] at hh
    linarith
  refine ⟨t₀,τ₀,Δ,ht,hτ,hτle,hΔ,?_⟩
  intro t τ x htt hττ hx
  obtain ⟨ha,hb⟩:=h t τ x htt hττ hx
  constructor
  · exact ha.trans (min_le_left _ _)
  · convert hb using 1 <;> ring
end Oberwolfach
