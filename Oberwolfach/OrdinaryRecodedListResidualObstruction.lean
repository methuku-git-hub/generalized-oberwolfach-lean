module

public import Oberwolfach.OrdinaryRecodedListRateChoice

@[expose] public section
/-! The currently used recoded-list lower bound and generic forced-placement
size condition cannot be instantiated together at the same parameter θ. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_recoded_list_residual_obstruction
    (θ γ pstar β lam ζ δ n d:ℝ)
    (hθ:0<θ) (hθ1:θ≤1) (hγ:0≤γ) (hγ1:γ≤1)
    (hp:0≤pstar) (hp1:pstar≤1) (hlam:0≤lam) (hζ:0≤ζ)
    (hn:0<n) (hd:0<d)
    (hlist:β*n+n^(3/4:ℝ)≤(γ*pstar^2)*n*(θ/2))
    (hmarg:(lam+2*ζ)*n+(n+2*n^(3/4:ℝ))/d≤β*n)
    (hresidual:2*θ≤δ) (hplacement:δ≤(lam/100)^2):False :=by
  have hp2:pstar^2≤1:=by nlinarith
  have hprod:γ*pstar^2≤1:=by
    calc
      γ*pstar^2≤1*pstar^2:=mul_le_mul_of_nonneg_right hγ1 (sq_nonneg _)
      _≤1:=by simpa using hp2
  have hpow:0≤n^(3/4:ℝ):=by positivity
  have hfrac:0≤(n+2*n^(3/4:ℝ))/d:=by positivity
  have hlamn:lam*n≤β*n:=by nlinarith [mul_nonneg hζ hn.le]
  have hlamβ:lam≤β:=by nlinarith
  have hcoeff:γ*pstar^2*(θ/2)≤θ/2:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod) (show 0≤θ/2 by positivity)]
  have hcoefn:=mul_le_mul_of_nonneg_right hcoeff hn.le
  have hβn:β*n≤(θ/2)*n:=by nlinarith [hcoefn]
  have hβθ:β≤θ/2:=by nlinarith
  have hlamθ:lam≤θ:=by linarith
  have hsq:lam^2≤θ^2:=by nlinarith [sq_nonneg (θ-lam)]
  have hθsq:θ^2≤θ:=by nlinarith
  nlinarith [sq_nonneg lam]
end Oberwolfach
