module

public import Oberwolfach.ApproximatePreparationTargetArithmetic

@[expose] public section
/-! The conflict losses and the host degree error fit the prescribed
positional tolerance once the order is large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem ordinary_positional_error_budget (r b:ℕ) (B τ:ℝ) (hB:0≤B) (hτ:0<τ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ D ε:ℝ,(n:ℝ)/2≤D→ε≤τ/4→
      5*(r:ℝ)^4*B*(2*b)/(n:ℝ)≤τ ∧
      6*(r:ℝ)^4*B*(2*b)+ε*(n:ℝ)≤τ*D:=by
  let E:ℝ:=5*(r:ℝ)^4*B*(2*b)
  let A:ℝ:=6*(r:ℝ)^4*B*(2*b)
  have hE:0≤E:=by dsimp [E];positivity
  have hA:0≤A:=by dsimp [A];positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (max (E/τ) (4*A/τ)+1)
  refine ⟨N,?_⟩
  intro n hn D ε hD hε
  have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
  have hx:(max (E/τ) (4*A/τ)+1)<(n:ℝ):=hN.trans_le hnR
  have hnpos:(0:ℝ)<n:=by
    have hh:0≤E/τ:=div_nonneg hE hτ.le
    have hmax:=le_max_left (E/τ) (4*A/τ)
    linarith
  have he:E/τ<(n:ℝ):=by have:=le_max_left (E/τ) (4*A/τ);linarith
  have ha:4*A/τ<(n:ℝ):=by have:=le_max_right (E/τ) (4*A/τ);linarith
  have he':E≤τ*n:=by simpa [mul_comm] using le_of_lt ((div_lt_iff₀ hτ).mp he)
  have ha':4*A≤τ*n:=by simpa [mul_comm] using le_of_lt ((div_lt_iff₀ hτ).mp ha)
  have heps:ε*(n:ℝ)≤(τ/4)*(n:ℝ):=mul_le_mul_of_nonneg_right hε hnpos.le
  constructor
  · exact (div_le_iff₀ hnpos).mpr he'
  · have hD':τ*(n:ℝ)/2≤τ*D:=by nlinarith [mul_le_mul_of_nonneg_left hD hτ.le]
    dsimp [A] at ha'
    nlinarith [ha',heps,hD']
end Oberwolfach
