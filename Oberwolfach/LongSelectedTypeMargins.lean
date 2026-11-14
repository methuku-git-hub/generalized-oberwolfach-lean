module

public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The selected marked density controls both type supplies. All deterministic
losses are paid at full size; no sampling factor is applied to them. -/
theorem long_selected_type_supply_margins
    (ρ₀ ρ N D rho err loss inner reserve:ℝ) (m:ℕ)
    (hρ₀:0<ρ₀) (hρ:ρ₀≤ρ) (hm:0<m) (hN:0≤N) (hD:N/2≤D)
    (hcost:rho*N+err+loss+inner+reserve≤ρ₀/(400*(m:ℝ))*N):
    let p:=ρ*(1/100:ℝ)/2
    let k:=ρ*((1/100:ℝ)/(m:ℝ))/2
    ∀p₂ k₂ u:ℝ,
      rho*N≤markedExpandedPhysicalProbability p k p₂ k₂ u 0/2*D-err-loss-inner-reserve ∧
      rho*N≤markedExpandedPhysicalProbability p k p₂ k₂ u 1/2*D-err-loss-inner-reserve:=by
  intro p k p₂ k₂ u
  have hmR:0<(m:ℝ):=by exact_mod_cast hm
  have hm1:1≤(m:ℝ):=by exact_mod_cast hm
  have hρpos:0<ρ:=lt_of_lt_of_le hρ₀ hρ
  have hk:0≤k:=by dsimp [k];positivity
  have hD0:0≤D:=le_trans (by positivity) hD
  have hpk:k≤p:=by
    dsimp [p,k]
    have ht:(1/100:ℝ)/(m:ℝ)≤1/100:=div_le_self (by positivity) hm1
    have hs:=mul_le_mul_of_nonneg_left ht hρpos.le
    linarith only [hs]
  have hklow:ρ₀/(400*(m:ℝ))≤k/2:=by
    dsimp [k]
    have hmul:0<400*(m:ℝ):=by positivity
    apply (div_le_iff₀ hmul).2
    field_simp
    nlinarith only [hρ]
  have hkd:ρ₀/(400*(m:ℝ))*N≤k*D:=by
    have h₁:=mul_le_mul_of_nonneg_right hklow hN
    have h₂:=mul_le_mul_of_nonneg_left hD hk
    nlinarith only [h₁,h₂]
  have hpd:k*D≤p*D:=mul_le_mul_of_nonneg_right hpk hD0
  constructor <;>
    simp only [markedExpandedPhysicalProbability,Matrix.cons_val_zero,Matrix.cons_val_one] <;>
    nlinarith only [hcost,hkd,hpd]
end Oberwolfach
