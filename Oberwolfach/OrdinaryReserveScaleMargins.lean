module

public import Oberwolfach.OrdinaryEditRateMargins

@[expose] public section
/-! Small reserve density and sampling error give the required physical
degree scale simultaneously in the rim and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reserve_rate_choice (ω ζ:ℝ) (hω:0<ω) (hζ:0<ζ):
    ∃pmax εmax:ℝ,0<pmax ∧ 0<εmax ∧ ∀p ε:ℝ,0≤p→0≤ε→p≤pmax→ε≤εmax→
      p+ε≤ζ*min 1 ω/2:=by
  let t:=ζ*min 1 ω/8
  have ht:0<t:=by dsimp [t];positivity
  refine ⟨t,t,ht,ht,?_⟩
  intro p ε _ _ hp he
  dsimp [t] at hp he
  have hprod:0≤ζ*min 1 ω:=by positivity
  linarith only [hp,he,hprod]

theorem ordinary_reserve_scale_from_hub_ratio (ω ζ p ε:ℝ) (hω:0<ω) (hζ:0≤ζ)
    (hpe:0≤p+ε) (hsmall:p+ε≤ζ*min 1 ω/2)
    (n m:ℕ) (hupper:m≤n) (hlower:ω*n≤m):
    (p+ε)*(n+m:ℝ)≤ζ*n ∧ (p+ε)*(n+m:ℝ)≤ζ*m:=by
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hmn:(m:ℝ)≤n:=Nat.cast_le.mpr hupper
  have hmin1:min (1:ℝ) ω≤1:=min_le_left _ _
  have hminω:min (1:ℝ) ω≤ω:=min_le_right _ _
  have hc1:2*(p+ε)≤ζ:=by
    have hh:=mul_le_mul_of_nonneg_left hmin1 hζ
    nlinarith only [hsmall,hh]
  have hc2:2*(p+ε)≤ζ*ω:=by
    have hh:=mul_le_mul_of_nonneg_left hminω hζ
    nlinarith only [hsmall,hh]
  have hsum:(p+ε)*((n:ℝ)+m)≤(p+ε)*(2*n):=by
    apply mul_le_mul_of_nonneg_left _ hpe
    linarith only [hmn]
  have hn1:=mul_le_mul_of_nonneg_right hc1 hn
  have hn2:=mul_le_mul_of_nonneg_right hc2 hn
  have hm:=mul_le_mul_of_nonneg_left hlower hζ
  constructor <;> nlinarith only [hsum,hn1,hn2,hm]
end Oberwolfach
