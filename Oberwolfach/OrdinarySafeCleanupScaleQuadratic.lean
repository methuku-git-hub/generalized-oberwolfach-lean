module

public import Oberwolfach.OrdinarySafeCleanupScale

@[expose] public section
/-! For boundary parameters linear in the vortex scale, the explicit cleanup
tolerance has a uniform quadratic lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinarySafeCleanupQuadraticConstant (r:ℕ) (p a b c cap₀:ℝ):ℝ :=
  let A:ℝ:=4*(r:ℝ)+40
  let k:=min (1/2:ℝ) (min (p^3*a/(16*A)) (min (p^2*b/(8*A)) (c/(4*A))))
  min (k^2/2) cap₀

theorem ordinary_safe_cleanup_scale_quadratic_lower
    (r:ℕ) (p a b c cap₀ ε:ℝ) (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀)
    (hε:0≤ε) (hεone:ε≤1):
    0<ordinarySafeCleanupQuadraticConstant r p a b c cap₀ ∧
    ordinarySafeCleanupQuadraticConstant r p a b c cap₀*ε^2≤
      ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2) :=by
  let A:ℝ:=4*(r:ℝ)+40
  have hA:0<A:=by dsimp [A];positivity
  let k:=min (1/2:ℝ) (min (p^3*a/(16*A)) (min (p^2*b/(8*A)) (c/(4*A))))
  let K:=ordinarySafeCleanupQuadraticConstant r p a b c cap₀
  let κ:=min (1/2:ℝ) (min ((p^3*((a*ε)/2)/2)/(4*A))
    (min ((p^2*(b*ε)/2)/(4*A)) ((c*ε)/(4*A))))
  have hk:0<k:=by dsimp [k];positivity
  have hK:0<K:=by dsimp [K,ordinarySafeCleanupQuadraticConstant];exact lt_min (by positivity) hcap
  have hk₁:k≤1/2:=min_le_left _ _
  have hka:k≤p^3*a/(16*A):=(min_le_right _ _).trans (min_le_left _ _)
  have hkb:k≤p^2*b/(8*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkc:k≤c/(4*A):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hscale:ε*k≤κ:=by
    dsimp only [κ]
    refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
    · have hm:=mul_le_mul_of_nonneg_left hk₁ hε
      nlinarith only [hm,hεone]
    · have hm:=mul_le_mul_of_nonneg_left hka hε
      convert hm using 1 <;> ring
    · have hm:=mul_le_mul_of_nonneg_left hkb hε
      convert hm using 1 <;> ring
    · have hm:=mul_le_mul_of_nonneg_left hkc hε
      convert hm using 1 <;> ring
  have hκ:0≤κ:=(mul_nonneg hε hk.le).trans hscale
  have hsq:(ε*k)^2≤κ^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr hscale) (add_nonneg hκ (mul_nonneg hε hk.le))]
  have hKk:K≤k^2/2:=min_le_left _ _
  have hKcap:K≤cap₀:=min_le_right _ _
  have hleft:K*ε^2≤κ^2/2:=by
    have hm:=mul_le_mul_of_nonneg_right hKk (sq_nonneg ε)
    nlinarith only [hm,hsq]
  have hright:K*ε^2≤cap₀*ε^2:=mul_le_mul_of_nonneg_right hKcap (sq_nonneg ε)
  refine ⟨hK,?_⟩
  change K*ε^2≤min (κ^2/2) (cap₀*ε^2)
  exact le_min hleft hright
end Oberwolfach
