module

public import Oberwolfach.OrdinaryCleanupMarginHierarchy

@[expose] public section
/-! Choose the root and cover error budget after the pre-cover cleanup
coefficients, preserving half of each positive coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_root_cover_cleanup_margins (p βe₀ βh₀:ℝ)
    (hp:0<p) (he:0<βe₀) (hh:0<βh₀):
    ∃κ:ℝ,0<κ ∧ ∀n t η ell:ℝ,0≤n→t≤κ*n→η≤κ*n→ell≤κ*n→
      t≤((p^3*(βe₀/2)/2)/2)*n ∧
      (βe₀/2)*n+3*max η ell≤βe₀*n ∧
      (βh₀/2)*n+2*ell≤βh₀*n:=by
  let κ:=min (βe₀/12) (min (βh₀/8) (p^3*βe₀/16))
  have hκ:0<κ:=by dsimp [κ];positivity
  have hκe:κ≤βe₀/12:=min_le_left _ _
  have hκh:κ≤βh₀/8:=(min_le_right _ _).trans (min_le_left _ _)
  have hκt:κ≤p^3*βe₀/16:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ,hκ,?_⟩
  intro n t η ell hn ht hη hell
  have hmax:max η ell≤κ*n:=max_le hη hell
  have he' := mul_le_mul_of_nonneg_right hκe hn
  have hh' := mul_le_mul_of_nonneg_right hκh hn
  have ht' := mul_le_mul_of_nonneg_right hκt hn
  have hep:0≤βe₀*n:=mul_nonneg he.le hn
  have hhp:0≤βh₀*n:=mul_nonneg hh.le hn
  have htp:0≤(p^3*βe₀)*n:=by positivity
  constructor
  · nlinarith only [ht,ht',htp]
  · constructor <;> nlinarith only [hmax,hell,he',hh',hep,hhp]
end Oberwolfach
