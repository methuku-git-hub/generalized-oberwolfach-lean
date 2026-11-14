module

public import Oberwolfach.OrdinarySafeCleanupScale

@[expose] public section
/-! If the fresh-sampling rate and boundary allowances scale linearly with the
vortex parameter, the explicit cleanup scale has an eighth-power lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinarySafeCleanupFourteenthConstant (r:ℕ) (p a b c cap₀:ℝ):ℝ :=
  let A:ℝ:=4*(r:ℝ)+40
  let k:=min (1/2:ℝ) (min (p^3*a/(16*A)) (min (p^2*b/(8*A)) (c/(4*A))))
  min (k^2/2) cap₀

theorem ordinary_safe_cleanup_scale_fourteenth_lower
    (r:ℕ) (p a b c cap₀ ε:ℝ) (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hε:0≤ε) (hεone:ε≤1):
    0<ordinarySafeCleanupFourteenthConstant r p a b c cap₀ ∧
    ordinarySafeCleanupFourteenthConstant r p a b c cap₀*ε^14≤
      ordinarySafeCleanupScale r (p*ε^2) (a*ε) (b*ε) (c*ε) (cap₀*ε^14) :=by
  let A:ℝ:=4*(r:ℝ)+40
  have hA:0<A:=by dsimp [A];positivity
  let k:=min (1/2:ℝ) (min (p^3*a/(16*A)) (min (p^2*b/(8*A)) (c/(4*A))))
  let K:=ordinarySafeCleanupFourteenthConstant r p a b c cap₀
  let κ:=min (1/2:ℝ) (min (((p*ε^2)^3*((a*ε)/2)/2)/(4*A))
    (min (((p*ε^2)^2*(b*ε)/2)/(4*A)) ((c*ε)/(4*A))))
  have hk:0<k:=by dsimp [k];positivity
  have hK:0<K:=by dsimp [K,ordinarySafeCleanupFourteenthConstant];exact lt_min (by positivity) hcap
  have hk₁:k≤1/2:=min_le_left _ _
  have hka:k≤p^3*a/(16*A):=(min_le_right _ _).trans (min_le_left _ _)
  have hkb:k≤p^2*b/(8*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkc:k≤c/(4*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have he20:0≤ε^2:=sq_nonneg ε
  have he2one:ε^2≤1:=pow_le_one₀ hε hεone
  have he50:0≤ε^5:=pow_nonneg hε 5
  have he6one:ε^6≤1:=pow_le_one₀ hε hεone
  have he4:ε^7≤ε^5:=by
    have hh:=mul_le_mul_of_nonneg_right he2one he50
    nlinarith only [hh]
  have he41:ε^7≤1:=pow_le_one₀ hε hεone
  have he4e:ε^7≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right he6one hε
    nlinarith only [hh]
  have he40:0≤ε^7:=pow_nonneg hε 7
  have hscale:ε^7*k≤κ:=by
    dsimp only [κ]
    refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
    · have hm:=mul_le_mul_of_nonneg_left hk₁ he40
      nlinarith only [hm,he41]
    · have hm:=mul_le_mul_of_nonneg_left hka he40
      convert hm using 1 <;> ring
    · have hm:=mul_le_mul_of_nonneg_left hkb he40
      have hm':=(mul_le_mul_of_nonneg_left he4 (show 0≤p^2*b/(8*A) by positivity))
      have ht:ε^7*k≤ε^5*(p^2*b/(8*A)):=by nlinarith only [hm,hm']
      convert ht using 1 <;> ring
    · have hm:=mul_le_mul_of_nonneg_left hkc he40
      have hm':=(mul_le_mul_of_nonneg_left he4e (show 0≤c/(4*A) by positivity))
      have ht:ε^7*k≤ε*(c/(4*A)):=by nlinarith only [hm,hm']
      convert ht using 1 <;> ring
  have hκ:0≤κ:=(mul_nonneg he40 hk.le).trans hscale
  have hsq:(ε^7*k)^2≤κ^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr hscale) (add_nonneg hκ (mul_nonneg he40 hk.le))]
  have hKk:K≤k^2/2:=min_le_left _ _
  have hKcap:K≤cap₀:=min_le_right _ _
  have hleft:K*ε^14≤κ^2/2:=by
    have hm:=mul_le_mul_of_nonneg_right hKk (pow_nonneg hε 14)
    nlinarith only [hm,hsq]
  have hright:K*ε^14≤cap₀*ε^14:=mul_le_mul_of_nonneg_right hKcap (pow_nonneg hε 14)
  refine ⟨hK,?_⟩
  change K*ε^14≤min (κ^2/2) (cap₀*ε^14)
  exact le_min hleft hright
end Oberwolfach
