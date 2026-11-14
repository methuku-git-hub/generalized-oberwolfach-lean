module

public import Oberwolfach.OrdinarySafeCleanupScale

@[expose] public section
/-! If the fresh-sampling rate and boundary allowances scale linearly with the
vortex parameter, the explicit cleanup scale has an eighth-power lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinarySafeCleanupEighthConstant (r:ℕ) (p a b c cap₀:ℝ):ℝ :=
  let A:ℝ:=4*(r:ℝ)+40
  let k:=min (1/2:ℝ) (min (p^3*a/(16*A)) (min (p^2*b/(8*A)) (c/(4*A))))
  min (k^2/2) cap₀

theorem ordinary_safe_cleanup_scale_eighth_lower
    (r:ℕ) (p a b c cap₀ ε:ℝ) (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hε:0≤ε) (hεone:ε≤1):
    0<ordinarySafeCleanupEighthConstant r p a b c cap₀ ∧
    ordinarySafeCleanupEighthConstant r p a b c cap₀*ε^8≤
      ordinarySafeCleanupScale r (p*ε) (a*ε) (b*ε) (c*ε) (cap₀*ε^8) :=by
  let A:ℝ:=4*(r:ℝ)+40
  have hA:0<A:=by dsimp [A];positivity
  let k:=min (1/2:ℝ) (min (p^3*a/(16*A)) (min (p^2*b/(8*A)) (c/(4*A))))
  let K:=ordinarySafeCleanupEighthConstant r p a b c cap₀
  let κ:=min (1/2:ℝ) (min (((p*ε)^3*((a*ε)/2)/2)/(4*A))
    (min (((p*ε)^2*(b*ε)/2)/(4*A)) ((c*ε)/(4*A))))
  have hk:0<k:=by dsimp [k];positivity
  have hK:0<K:=by dsimp [K,ordinarySafeCleanupEighthConstant];exact lt_min (by positivity) hcap
  have hk₁:k≤1/2:=min_le_left _ _
  have hka:k≤p^3*a/(16*A):=(min_le_right _ _).trans (min_le_left _ _)
  have hkb:k≤p^2*b/(8*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkc:k≤c/(4*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have he2:ε^2≤ε:=by nlinarith [mul_nonneg hε (sub_nonneg.mpr hεone)]
  have he3:ε^3≤ε^2:=by nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hεone)]
  have he4:ε^4≤ε^3:=by nlinarith [mul_nonneg (pow_nonneg hε 3) (sub_nonneg.mpr hεone)]
  have he41:ε^4≤1:=by linarith
  have he4e:ε^4≤ε:=by linarith
  have he40:0≤ε^4:=pow_nonneg hε 4
  have hscale:ε^4*k≤κ:=by
    dsimp only [κ]
    refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
    · have hm:=mul_le_mul_of_nonneg_left hk₁ he40
      nlinarith only [hm,he41]
    · have hm:=mul_le_mul_of_nonneg_left hka he40
      convert hm using 1 <;> ring
    · have hm:=mul_le_mul_of_nonneg_left hkb he40
      have hm':=(mul_le_mul_of_nonneg_left he4 (show 0≤p^2*b/(8*A) by positivity))
      have ht:ε^4*k≤ε^3*(p^2*b/(8*A)):=by nlinarith only [hm,hm']
      convert ht using 1 <;> ring
    · have hm:=mul_le_mul_of_nonneg_left hkc he40
      have hm':=(mul_le_mul_of_nonneg_left he4e (show 0≤c/(4*A) by positivity))
      have ht:ε^4*k≤ε*(c/(4*A)):=by nlinarith only [hm,hm']
      convert ht using 1 <;> ring
  have hκ:0≤κ:=(mul_nonneg he40 hk.le).trans hscale
  have hsq:(ε^4*k)^2≤κ^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr hscale) (add_nonneg hκ (mul_nonneg he40 hk.le))]
  have hKk:K≤k^2/2:=min_le_left _ _
  have hKcap:K≤cap₀:=min_le_right _ _
  have hleft:K*ε^8≤κ^2/2:=by
    have hm:=mul_le_mul_of_nonneg_right hKk (pow_nonneg hε 8)
    nlinarith only [hm,hsq]
  have hright:K*ε^8≤cap₀*ε^8:=mul_le_mul_of_nonneg_right hKcap (pow_nonneg hε 8)
  refine ⟨hK,?_⟩
  change K*ε^8≤min (κ^2/2) (cap₀*ε^8)
  exact le_min hleft hright
end Oberwolfach
