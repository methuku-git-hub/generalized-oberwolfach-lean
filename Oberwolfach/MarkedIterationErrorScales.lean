module

public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Numerical choices for successive marked cover-down calls. The
analytic tolerance precedes the star-loss allowance; the correction and
initial inner-root balance tolerance can subsequently be chosen smaller. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Oberwolfach

theorem marked_iteration_reference_scale
    (h : ℕ) (κ γ p k omega C : ℝ)
    (hκ : 0<κ) (hγ : 0<γ) (hp : 0<p) (hk : 0<k) (ho : 0<omega) (hC : 0≤C) :
    ∃ ζmax : ℝ,0<ζmax ∧ ∀ ε ζ : ℝ,ε≤κ/4→0≤ζ→ζ≤ζmax→
      ε+ζ≤κ ∧ ε+4*ζ≤κ ∧ ε+2*h*ζ≤κ ∧ ε+h*ζ≤κ ∧
      ζ≤(κ-ε)*omega ∧ ε≤κ ∧ 2*ζ≤(3/4)*γ*p^2 ∧ ζ≤γ*min p k/8 ∧ C*ζ≤κ/4 := by
  let ζmax := min (κ/8) (min (κ/(8*((h:ℝ)+1)))
    (min (κ*omega/8) (min (γ*p^2/8) (min (γ*min p k/16) (κ/(4*(C+1)))))))
  have hz : 0<ζmax := by dsimp [ζmax];positivity
  refine ⟨ζmax,hz,?_⟩
  intro ε ζ he hζ hzmax
  have hz1 : ζ≤κ/8 := hzmax.trans (min_le_left _ _)
  have hzt := hzmax.trans (min_le_right _ _)
  have hz2 : ζ≤κ/(8*((h:ℝ)+1)) := hzt.trans (min_le_left _ _)
  have hzt := hzt.trans (min_le_right _ _)
  have hz3 : ζ≤κ*omega/8 := hzt.trans (min_le_left _ _)
  have hzt := hzt.trans (min_le_right _ _)
  have hz4 : ζ≤γ*p^2/8 := hzt.trans (min_le_left _ _)
  have hzt := hzt.trans (min_le_right _ _)
  have hz5 : ζ≤γ*min p k/16 := hzt.trans (min_le_left _ _)
  have hz6 : ζ≤κ/(4*(C+1)) := hzt.trans (min_le_right _ _)
  have hz2' := (le_div_iff₀ (show 0<8*((h:ℝ)+1) by positivity)).mp hz2
  have hz6' := (le_div_iff₀ (show 0<4*(C+1) by positivity)).mp hz6
  have hω := mul_le_mul_of_nonneg_right he ho.le
  have hgpp : 0≤γ*p^2 := by positivity
  have hgpk : 0≤γ*min p k := by positivity
  refine ⟨by linarith only [he,hz1,hκ],by linarith only [he,hz1,hκ],
    by nlinarith only [he,hz2',hζ,hκ],by nlinarith only [he,hz2',hζ,hκ],
    by nlinarith only [hz3,hω,mul_pos hκ ho],by linarith only [he,hκ],
    by nlinarith only [hz4,hgpp],by linarith only [hz5,hgpk],?_⟩
  nlinarith only [hz6',hζ]

theorem marked_iteration_star_scale
    (m : ℕ) (x eps C b theta : ℝ)
    (hx : 0<x) (heps : 0<eps) (hC : 0≤C) (hb : 0<b) (htheta : 0<theta) :
    ∃ sigmaMax : ℝ,0<sigmaMax ∧ ∀ sigma : ℝ,0≤sigma→sigma≤sigmaMax→
      (m+2)*sigma≤x/4 ∧ 4*C*sigma/eps≤x/4 ∧
      4*C*sigma/eps≤b/4 ∧ 4*C*sigma/eps≤theta/4 := by
  let sigmaMax := min (x/(4*((m:ℝ)+2))) (eps*min x (min b theta)/(16*(C+1)))
  refine ⟨sigmaMax,by dsimp [sigmaMax];positivity,?_⟩
  intro sigma hs hsmall
  have h1 := hsmall.trans (min_le_left _ _)
  have h2 := hsmall.trans (min_le_right _ _)
  have h1' := (le_div_iff₀ (show 0<4*((m:ℝ)+2) by positivity)).mp h1
  have h2' := (le_div_iff₀ (show 0<16*(C+1) by positivity)).mp h2
  have h2x := mul_le_mul_of_nonneg_left (min_le_left x (min b theta)) heps.le
  have h2b := mul_le_mul_of_nonneg_left ((min_le_right x (min b theta)).trans (min_le_left b theta)) heps.le
  have h2t := mul_le_mul_of_nonneg_left ((min_le_right x (min b theta)).trans (min_le_right b theta)) heps.le
  refine ⟨by nlinarith only [h1'],?_,?_,?_⟩
  all_goals apply (div_le_iff₀ heps).mpr
  · nlinarith only [h2',h2x,hs]
  · nlinarith only [h2',h2b,hs]
  · nlinarith only [h2',h2t,hs]

theorem marked_iteration_local_normalization
    (C sigma eps n a budget : ℝ)
    (hC : 0≤C) (hs : 0≤sigma) (heps : 0<eps) (hn : 0≤n) (ha : 0<a)
    (hsize : eps*n/4≤a) (hbudget : 4*C*sigma/eps≤budget) :
    C*(sigma*n)/a≤budget := by
  apply le_trans _ hbudget
  apply (div_le_iff₀ ha).mpr
  have hm := mul_le_mul_of_nonneg_left hsize (show 0≤4*C*sigma/eps by positivity)
  have he : (4*C*sigma/eps)*(eps*n/4)=C*(sigma*n) := by field_simp
  rw [he] at hm
  exact hm

theorem marked_iteration_all_root_balance_budget
    (m : ℕ) (base sigma x n a : ℝ)
    (hn : 0≤n) (ha : 0≤a) (hsize : a≤n) (hx : 0≤x)
    (hbase : base≤x/2) (hstar : (m+2)*sigma≤x/4) :
    base*a+(m+2)*(sigma*n)≤x*n := by
  have h1 := mul_le_mul_of_nonneg_right hbase ha
  have h2 := mul_le_mul_of_nonneg_right hstar hn
  have h3 := mul_le_mul_of_nonneg_left hsize (show 0≤x/2 by positivity)
  nlinarith only [h1,h2,h3,mul_nonneg hx hn]

end Oberwolfach
