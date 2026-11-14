module

public import Oberwolfach.LongMatchingUniformTolerances

@[expose] public section
/-! Fixed positive sub-tolerances also supply the ordinary factor-assignment
and hub-count margins, uniformly over all permitted deletions. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_assignment_uniform_tolerances_exist
    (t₀ τ₀ Δ₀ C eps:ℝ) (ht₀:0<t₀) (hτ₀:0<τ₀) (hΔ₀:0<Δ₀) (hC:0≤C) (heps:0<eps):
    ∃t₁ τ₁ Δ₁ ξ:ℝ,0<t₁ ∧ t₁≤t₀ ∧ 0<τ₁ ∧ τ₁≤τ₀ ∧ 0<Δ₁ ∧ Δ₁≤Δ₀ ∧
      0<ξ ∧ ξ≤1/16 ∧ 4*ξ≤eps/2 ∧
      ∀t τ x:ℝ,0≤t → t≤t₁ → 0≤τ → τ≤τ₁ → 0≤x → x≤Δ₁ →
        0≤t+C*x+4*τ ∧ t+C*x+4*τ≤eps/2 :=by
  let t₁:=min t₀ (eps/8)
  let τ₁:=min τ₀ (eps/32)
  let Δ₁:=min Δ₀ (eps/(8*(C+1)))
  let ξ:=min (1/16:ℝ) (eps/16)
  have ht:0<t₁:=lt_min ht₀ (by positivity)
  have hτ:0<τ₁:=lt_min hτ₀ (by positivity)
  have hΔ:0<Δ₁:=lt_min hΔ₀ (by positivity)
  have hξ:0<ξ:=lt_min (by norm_num) (by positivity)
  have hξeps:4*ξ≤eps/2:=by
    have hh:ξ≤eps/16:=min_le_right _ _
    linarith
  refine ⟨t₁,τ₁,Δ₁,ξ,ht,min_le_left _ _,hτ,min_le_left _ _,hΔ,min_le_left _ _,hξ,min_le_left _ _,hξeps,?_⟩
  intro t τ x ht0 htt hτ0 hττ hx0 hxΔ
  have htb:t≤eps/8:=htt.trans (min_le_right _ _)
  have hτb:τ≤eps/32:=hττ.trans (min_le_right _ _)
  have hxb:x≤eps/(8*(C+1)):=hxΔ.trans (min_le_right _ _)
  have hCx:C*x≤eps/8:=by
    have hh:=mul_le_mul_of_nonneg_left hxb hC
    have hden:0<8*(C+1):=by positivity
    have hb:C*(eps/(8*(C+1)))≤eps/8:=by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).2
      have hc:C/(C+1)≤1:=by
        apply (div_le_iff₀ (by positivity : 0<C+1)).2
        linarith
      have he:=mul_le_mul_of_nonneg_left hc heps.le
      field_simp at hh ⊢
      nlinarith
    exact hh.trans hb
  constructor
  · positivity
  · linarith
end Oberwolfach
