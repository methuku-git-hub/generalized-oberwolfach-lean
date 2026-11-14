module

public import Oberwolfach.OrdinaryNonrootWeightMargins

@[expose] public section
/-! Choose one relative root-size scale after the parent constants, small
enough for cuts, configuration counts, degrees and weighted loads. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem ordinary_nonroot_root_scale_choice (r:ℕ) (β δ ω gap B:ℝ)
    (hβ:0<β) (hδ:0<δ) (hω:0<ω) (hgap:0<gap) (hB:0≤B):
    ∃lam:ℝ,0<lam ∧ ∀n m t w:ℝ,0≤n→0≤w→w≤t→t≤lam*n→ω*n≤m→
      t≤δ*n ∧ w≤δ*m ∧ w≤(β/2)*n ∧ t*(r:ℝ)^2≤(β/2)*n ∧
      lam*(r:ℝ)^4*B≤gap:=by
  let a:ℝ:=(r:ℝ)^2+1
  let c:ℝ:=(r:ℝ)^4*B+1
  have ha:0<a:=by dsimp [a];positivity
  have hc:0<c:=by dsimp [c];positivity
  let lam:=min (δ/2) (min (δ*ω/2) (min (β/(4*a)) (gap/(2*c))))
  have hlam:0<lam:=by dsimp [lam];positivity
  have hlamδ:lam≤δ/2:=min_le_left _ _
  have hlamω:lam≤δ*ω/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hlamβ:lam≤β/(4*a):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamgap:lam≤gap/(2*c):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hβmul:lam*(4*a)≤β:=(le_div_iff₀ (by positivity:0<4*a)).mp hlamβ
  have hgapmul:lam*(2*c)≤gap:=(le_div_iff₀ (by positivity:0<2*c)).mp hlamgap
  have hr2:0≤(r:ℝ)^2:=sq_nonneg _
  have hr4B:0≤(r:ℝ)^4*B:=mul_nonneg (by positivity) hB
  have hlamβ':lam≤β/2:=by dsimp [a] at hβmul;nlinarith only [hβmul,hlam.le,hr2]
  have hlamr:lam*(r:ℝ)^2≤β/2:=by dsimp [a] at hβmul;nlinarith only [hβmul,hlam.le,hr2]
  have hlamg:lam*(r:ℝ)^4*B≤gap:=by dsimp [c] at hgapmul;nlinarith only [hgapmul,hlam.le,hr4B]
  refine ⟨lam,hlam,?_⟩
  intro n m t w hn hw hwt ht hm
  have hd:=mul_le_mul_of_nonneg_right hlamδ hn
  have ho:=mul_le_mul_of_nonneg_right hlamω hn
  have hb:=mul_le_mul_of_nonneg_right hlamβ' hn
  have hr:=mul_le_mul_of_nonneg_right hlamr hn
  have hm':=mul_le_mul_of_nonneg_left hm hδ.le
  have ht':=mul_le_mul_of_nonneg_right ht hr2
  have hδn:0≤δ*n:=mul_nonneg hδ.le hn
  have hδωn:0≤(δ*ω)*n:=by positivity
  refine ⟨?_,?_,?_,?_,hlamg⟩
  · nlinarith only [ht,hd,hδn]
  · nlinarith only [hwt,ht,ho,hm',hδωn]
  · nlinarith only [hwt,ht,hb]
  · nlinarith only [ht',hr]
end Oberwolfach
