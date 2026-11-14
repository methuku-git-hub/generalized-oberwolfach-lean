module

public import Oberwolfach.OrdinaryBoundarySmallDensityChoice

@[expose] public section
/-! Choose reserve, cleanup and packing scales in the order used by the
boundary construction; the final order threshold absorbs rounding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_boundary_full_selection_scales (κ ζ pmax:ℝ) (hκ:0<κ) (hζ:0<ζ) (hpmax:0<pmax):
    ∃p ν:ℝ,0<p ∧ p≤1 ∧ p≤pmax ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<ν ∧ ν≤ζ*κ*p/4 ∧ ∀τ₀:ℝ,0<τ₀→∃τ:ℝ,0<τ ∧ τ≤τ₀ ∧ τ+ν≤p^2/4 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤ζ*κ*p*n/4:=by
  obtain ⟨p,hp,hp1,hpmax',hpκ,hsqrt⟩:=ordinary_boundary_small_density_choice κ ζ pmax hκ hζ hpmax
  let ν:=min (p^2/16) (ζ*κ*p/16)
  have hν:0<ν:=lt_min (by positivity) (by positivity)
  have hνp:ν≤p^2/16:=min_le_left _ _
  have hνκ:ν≤ζ*κ*p/16:=min_le_right _ _
  refine ⟨p,ν,hp,hp1,hpmax',hpκ,hsqrt,hν,?_,?_⟩
  · have hh:0≤ζ*κ*p:=by positivity
    linarith only [hνκ,hh]
  · intro τ₀ hτ₀
    let τ:=min (τ₀/2) (p^2/16)
    have hτ:0<τ:=lt_min (by positivity) (by positivity)
    have hτ₀':τ≤τ₀:=by have hh:=min_le_left (τ₀/2) (p^2/16);linarith
    have hτp:τ≤p^2/16:=min_le_right _ _
    refine ⟨τ,hτ,hτ₀',by nlinarith only [hτp,hνp,sq_nonneg p],?_⟩
    obtain ⟨N,hN⟩:=exists_nat_gt (8/(ζ*κ*p))
    refine ⟨N,?_⟩
    intro n hn
    have hnR:(N:ℝ)≤n:=Nat.cast_le.mpr hn
    have hh:8/(ζ*κ*p)≤(n:ℝ):=hN.le.trans hnR
    have hmul:8≤(n:ℝ)*(ζ*κ*p):=(div_le_iff₀ (by positivity:0<ζ*κ*p)).mp hh
    nlinarith only [hmul]
end Oberwolfach
