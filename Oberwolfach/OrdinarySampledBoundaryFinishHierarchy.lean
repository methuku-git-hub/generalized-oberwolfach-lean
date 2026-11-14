module

public import Oberwolfach.OrdinaryBoundaryCompletionAvailable
public import Oberwolfach.OrdinaryBoundarySmallDensityChoice

@[expose] public section
/-! The fresh density, selection errors, cleanup scales and endpoint
completion capacity can be chosen in a compatible order using the full
protected-inner extension coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_sampled_boundary_finish_ordered_hierarchy (m:ℕ) (β κ ζ:ℝ)
    (hβ:0<β) (hκ:0<κ) (hζ:0<ζ):
    ∃k p ε τ ν:ℝ,0<k ∧ 0<p ∧ 0<ε ∧ 0<τ ∧ 0<ν ∧
      p≤1 ∧ p≤4*ζ*min (κ/2) 1 ∧ 20*Real.sqrt (2*p)≤ζ*min (κ/2) 1/2 ∧
      ε≤p^2/4 ∧ τ+ν≤p^2/4 ∧ ν≤ζ*min (κ/2) 1*p/4 ∧ 2*p≤k^2 ∧ ν≤k^2 ∧
      ∀φ:ℝ,0≤φ→φ≤k^2→∃N:ℕ,
        ∀n:ℕ,N≤n→2≤ζ*min (κ/2) 1*p*n/4 ∧
          ∀Lconf:ℝ,Lconf≤φ*n→
          ∃D K:ℕ,0<K ∧ 2*p*n≤(D:ℝ) ∧
            ((n*D*(m+1):ℕ):ℝ)/(K:ℝ)+(((m+1:ℕ):ℝ)+3)*(Lconf+1)+
            2*(2*((2*p)*n)+2*((K+D:ℕ):ℝ))+(D:ℝ)+((D*(m+1):ℕ):ℝ)+3*D < β*n-3*(ν*n):=by
  let κ₀:=min (κ/2) 1
  have hκ₀:0<κ₀:=lt_min (by positivity) (by norm_num)
  obtain ⟨k,hk,hcap⟩:=ordinary_boundary_completion_available m β hβ
  obtain ⟨p,hp,hp1,hpmax,hpk,hpsqrt⟩:=ordinary_boundary_small_density_choice κ₀ ζ (k^2/4)
    hκ₀ hζ (by positivity)
  let ε:=p^2/8
  let τ:=min (p^2/16) (min (ζ*κ₀*p/16) (k^2/4))
  let ν:=τ
  have hε:0<ε:=by dsimp [ε];positivity
  have hτ:0<τ:=by dsimp [τ];positivity
  have hν:0<ν:=hτ
  have hτp:τ≤p^2/16:=min_le_left _ _
  have hτκ:τ≤ζ*κ₀*p/16:=(min_le_right _ _).trans (min_le_left _ _)
  have hτk:τ≤k^2/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hεbound:ε≤p^2/4:=by dsimp [ε];nlinarith [sq_nonneg p]
  have hsum:τ+ν≤p^2/4:=by dsimp [ν];nlinarith only [hτp,sq_nonneg p]
  have hνbound:ν≤ζ*κ₀*p/4:=by dsimp [ν];nlinarith [mul_pos (mul_pos hζ hκ₀) hp]
  have hpkhalf:2*p≤k^2/2:=by linarith
  have hpk2:2*p≤k^2:=by nlinarith [sq_nonneg k]
  have hνk:ν≤k^2:=by dsimp [ν];nlinarith [sq_nonneg k]
  refine ⟨k,p,ε,τ,ν,hk,hp,hε,hτ,hν,hp1,hpk,hpsqrt,hεbound,hsum,hνbound,hpk2,hνk,?_⟩
  intro φ hφ hφk
  obtain ⟨Ncap,hNcap⟩:=hcap (k^2) φ (2*p) ν (sq_nonneg k) hφ le_rfl hφk hpk2 hνk
  let N:=max Ncap (max ⌈8/(ζ*κ₀*p)⌉₊ ⌈2/k^2⌉₊)
  refine ⟨N,?_⟩
  intro n hn
  have hden:0<ζ*κ₀*p:=mul_pos (mul_pos hζ hκ₀) hp
  have hk2:0<k^2:=sq_pos_of_pos hk
  have hnsize:8/(ζ*κ₀*p)≤(n:ℝ):=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈8/(ζ*κ₀*p)⌉₊≤n from
      (le_max_left _ _).trans ((le_max_right _ _).trans hn)))
  have hnround:2/k^2≤(n:ℝ):=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2/k^2⌉₊≤n from
      (le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have horder:2≤ζ*κ₀*p*n/4:=by
    have hh:8≤(n:ℝ)*(ζ*κ₀*p):=(div_le_iff₀ hden).mp hnsize
    nlinarith only [hh]
  have hround:1≤(k^2/2)*n:=by
    have hh:2≤(n:ℝ)*k^2:=(div_le_iff₀ hk2).mp hnround
    nlinarith only [hh]
  refine ⟨horder,?_⟩
  intro Lconf hL
  let D:=⌈(2*p)*n⌉₊
  have hDlo:(2*p)*n≤(D:ℝ):=Nat.le_ceil _
  have hDhi:(D:ℝ)≤(2*p)*n+1:=(Nat.ceil_lt_add_one (by positivity:0≤(2*p)*(n:ℝ))).le
  have hn0:0≤(n:ℝ):=by positivity
  have hDn:(D:ℝ)≤k^2*n:=by
    have hh:=mul_le_mul_of_nonneg_right hpkhalf hn0
    nlinarith only [hh,hDhi,hround]
  obtain ⟨K,hK,hbudget⟩:=hNcap n ((le_max_left _ _).trans hn) D Lconf (ν*n) hDn hL le_rfl
  exact ⟨D,K,hK,hDlo,hbudget⟩
end Oberwolfach
