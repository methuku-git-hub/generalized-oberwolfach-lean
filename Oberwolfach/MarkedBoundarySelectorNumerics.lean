module

public import Oberwolfach.SelectionSmallDensityBudget

@[expose] public section

/-! Quantitative margins for the actual marked boundary selector. The
relative tolerance precedes the reservation probability; only the order
threshold depends on the separation radius. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem marked_boundary_selector_numerics (p₀ a g:ℝ)
    (hp₀:0<p₀) (ha:0<a) (hg:0<g):
    ∃ ε:ℝ,0<ε∧∀ ζ ω:ℝ,0<ζ→0<ω→∃ pmax:ℝ,0<pmax∧pmax≤1/8∧∀ p:ℝ,0<p→p≤pmax→∀ d:ℕ,∃ N:ℕ,
    ∀ n:ℕ,N≤n→∃ degree tau loss:ℝ,
      0<tau∧2*tau+(2*(2*(3*d)+1):ℕ)≤degree∧(2*(2*(3*d)+1):ℕ)<(p₀/4)*tau∧
      2*tau≤(g/2)*p*n∧loss≤(p₀/4)*tau∧loss≤ζ*p*(ω*n)∧
      (∀ s:ℝ,(a/2)*p*n≤s→s≤2*p*n→degree+loss≤(p₀/2)*s∧ε*s≤tau)∧
      4*(14*p*Real.sqrt (14*p)*n)+4*(Nat.ceil (4*(14*p*Real.sqrt (14*p)*n)):ℝ)+p^3*n≤loss∧
      2*((p^9+p^3)*n)≤p^2*n/2∧(p^9+p^3)*n≤ζ*p*(ω*n):=by
  let κ:=p₀*a/8
  let ξ:=min (p₀*a/64) (g/8)
  have hκ:0<κ:=by dsimp [κ];positivity
  have hξ:0<ξ:=lt_min (by positivity) (by positivity)
  have hξκ:8*ξ≤κ:=by have h:=min_le_left (p₀*a/64) (g/8);dsimp [ξ,κ];linarith
  have hξg:ξ≤g/8:=min_le_right _ _
  refine ⟨ξ/4,by positivity,?_⟩
  intro ζ ω hζ hω
  let L:=min (p₀*ξ/8) (min (ζ*ω/4) (κ/2))
  have hL:0<L:=lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hLξ:L≤p₀*ξ/8:=min_le_left _ _
  have hLζ:L≤ζ*ω/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hLκ:L≤κ/2:=(min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨pS,hpS,hpS1,hS⟩:=indexed_selection_small_density_budget 14 L (by norm_num) hL
  let pmax:=min pS (min (1/8) (min (L/4) (ζ*ω/8)))
  have hpmax:0<pmax:=lt_min hpS (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hpmax8:pmax≤1/8:=(min_le_right _ _).trans (min_le_left _ _)
  refine ⟨pmax,hpmax,hpmax8,?_⟩
  intro p hp hpp d
  have hp8:p≤1/8:=hpp.trans hpmax8
  have hp1:p≤1:=by linarith
  have hpL:p≤L/4:=hpp.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpζ:p≤ζ*ω/8:=hpp.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hp2:p^2≤p:=by nlinarith only [hp.le,hp1]
  have hp9:p^9≤p^3:=by
    calc
      p^9=p^3*p^6:=by ring
      _≤p^3*1:=mul_le_mul_of_nonneg_left (pow_le_one₀ hp.le hp1) (by positivity)
      _=p^3:=mul_one _
  obtain ⟨NS,hNS⟩:=hS p hp (hpp.trans (min_le_left _ _))
  let B:ℝ:=(2*(2*(3*d)+1):ℕ)
  obtain ⟨N,hN⟩:=exists_nat_gt (max 1 (max (4*B/(κ*p)) (8*B/(p₀*ξ*p))))
  refine ⟨max NS N,?_⟩
  intro n hn
  have hnR:(N:ℝ)≤n:=Nat.cast_le.mpr (show N≤n by omega)
  have hlarge:=hN.trans_le hnR
  have hnpos:(0:ℝ)<n:=lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hlarge.le)
  have hdeg:4*B<κ*p*n:=by
    have h:4*B/(κ*p)<(n:ℝ):=((le_max_left _ _).trans (le_max_right _ _)).trans_lt hlarge
    nlinarith only [(div_lt_iff₀ (mul_pos hκ hp)).mp h]
  have hsep:8*B<p₀*ξ*p*n:=by
    have h:8*B/(p₀*ξ*p)<(n:ℝ):=((le_max_right _ _).trans (le_max_right _ _)).trans_lt hlarge
    nlinarith only [(div_lt_iff₀ (by positivity:(0:ℝ)<p₀*ξ*p)).mp h]
  let degree:=κ*p*n
  let tau:=ξ*p*n
  let loss:=L*p*n
  refine ⟨degree,tau,loss,by dsimp [tau];positivity,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have h:=mul_le_mul_of_nonneg_right hξκ (show 0≤p*n by positivity)
    dsimp [degree,tau]
    change 2*(ξ*p*n)+B≤κ*p*n
    have hpos:0≤κ*p*n:=by positivity
    nlinarith only [h,hdeg,hpos]
  · dsimp [tau]
    change B<(p₀/4)*(ξ*p*n)
    have hB:0≤B:=by dsimp [B];positivity
    nlinarith only [hsep,hB]
  · have h:=mul_le_mul_of_nonneg_right hξg (show 0≤p*n by positivity)
    dsimp [tau]
    have hgn:0≤g*p*n:=by positivity
    nlinarith only [h,hgn]
  · have h:=mul_le_mul_of_nonneg_right hLξ (show 0≤p*n by positivity)
    dsimp [loss,tau]
    have hpos:0≤p₀*ξ*p*n:=by positivity
    nlinarith only [h,hpos]
  · have h:=mul_le_mul_of_nonneg_right hLζ (show 0≤p*n by positivity)
    dsimp [loss]
    have hpos:0≤ζ*ω*p*n:=by positivity
    nlinarith only [h,hpos]
  · intro s hs hsmax
    constructor
    · have h:=mul_le_mul_of_nonneg_right hLκ (show 0≤p*n by positivity)
      have hh:=mul_le_mul_of_nonneg_left hs hp₀.le
      have hpos:0≤κ*p*n:=by positivity
      dsimp [degree,loss,κ] at *
      nlinarith only [h,hh,hpos]
    · have h:=mul_le_mul_of_nonneg_left hsmax (show 0≤ξ/4 by positivity)
      dsimp [tau]
      have hpos:0≤ξ*p*n:=by positivity
      nlinarith only [h,hpos]
  · apply hNS n (by omega) (p^3*n)
    have h:=mul_le_mul_of_nonneg_right (hp2.trans hpL) (show 0≤p*n by positivity)
    have hpos:0≤L*p*n:=by positivity
    nlinarith only [h,hpos]
  · have h9:=mul_le_mul_of_nonneg_right hp9 hnpos.le
    have h:=mul_le_mul_of_nonneg_right hp8 (show 0≤p^2*n by positivity)
    nlinarith only [h9,h]
  · have h9:=mul_le_mul_of_nonneg_right hp9 hnpos.le
    have h:=mul_le_mul_of_nonneg_right (hp2.trans hpζ) (show 0≤p*n by positivity)
    have hpos:0≤ζ*ω*p*n:=by positivity
    nlinarith only [h9,h,hpos]
end Oberwolfach
