module

public import Oberwolfach.OrdinaryTriangleParameterSelection

@[expose] public section
/-! Translate the selected constant into the finite numerical bounds needed
by the prescribed and triangle constructions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_scaled_budgets
    (κ p γ ω η ρ ρhub θ n u L I J T C:ℝ)
    (hκ:0≤κ) (hp:0≤p) (hγ:0≤γ) (hω:0<ω) (hn:0≤n)
    (hscale:48*κ≤p^6*γ*min 1 ω) (hρhub:13*κ≤ρhub) (hρ:54*κ≤ρ)
    (hθη:κ≤θ) (hbalance:3*κ≤2*ω*p*η)
    (hu:ω*n≤u) (hL:0≤L) (hLsmall:L≤κ*n)
    (hI:0≤I) (hIsmall:I≤κ*n) (hJ:0≤J) (hJsmall:J≤κ*n)
    (hT:0≤T) (hTsmall:T≤κ*n) (hC:C≤ρ*n/2):
    let L':=13*κ*n;
    0≤L' ∧ 6*L≤(p^6*γ/4)*n ∧ 6*L≤(p^6*γ/4)*u ∧
      I≤p^6*γ*n/8 ∧ J≤p^6*γ*u/8 ∧ L+12*κ*n≤L' ∧
      L'≤ρhub*n ∧ 2*L'+T+C≤ρ*n ∧ T≤θ*n ∧ 0≤κ*n:=by
  intro L'
  have ht:0≤p^6*γ:=mul_nonneg (pow_nonneg hp _) hγ
  have hm1:p^6*γ*min 1 ω≤p^6*γ:=by nlinarith [mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) ω) ht]
  have hm2:p^6*γ*min 1 ω≤p^6*γ*ω:=mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) ω) ht
  have hv:48*κ≤p^6*γ:=hscale.trans hm1
  have hw:48*κ≤p^6*γ*ω:=hscale.trans hm2
  have hvn:=mul_le_mul_of_nonneg_right hv hn
  have hwn:=mul_le_mul_of_nonneg_right hw hn
  have hun:=mul_le_mul_of_nonneg_left hu ht
  have hhubn:=mul_le_mul_of_nonneg_right hρhub hn
  have hrhon:=mul_le_mul_of_nonneg_right hρ hn
  have hthetan:=mul_le_mul_of_nonneg_right hθη hn
  have hkn:0≤κ*n:=mul_nonneg hκ hn
  dsimp [L']
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,hkn⟩ <;> nlinarith only [hvn,hwn,hun,hhubn,hrhon,hthetan,hLsmall,hIsmall,hJsmall,hTsmall,hC,hkn]
end Oberwolfach
