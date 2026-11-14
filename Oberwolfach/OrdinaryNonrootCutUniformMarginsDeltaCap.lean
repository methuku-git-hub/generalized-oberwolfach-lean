module

public import Oberwolfach.OrdinarySampleProfileNonrootBothCuts

@[expose] public section
/-! Choose the elementary numerical cut margins before the host size and
actual spoke density, from a positive index ratio and density lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_cut_uniform_margins_with_delta_cap
    (ω pmin href δlimit:ℝ) (hω:0<ω) (hpmin:0<pmin) (hhrefpos:0<href) (hδlimit:0<δlimit):
    ∃h₀ δcut ζcut εcut ζlimit εsmall:ℝ,
      0<h₀ ∧ 0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsmall ∧
    ∀Dcut:ℕ,∃N:ℕ,1≤N ∧
    ∀I B pH tR tH L h:ℝ,
      (N:ℝ)≤I→0≤B→ω*I≤B→pmin≤pH→
      0≤tR→tR≤εsmall*I→0≤tH→tH≤εsmall*B→0≤L→L≤ζlimit*I→0≤h→h≤h₀→
      δcut≤pH/16 ∧ ζcut≤pH^2/128 ∧ 2*h≤pH/8 ∧ 2*h≤href-ζlimit ∧
      tH+2*L≤εcut*B ∧ tH+L≤pH*B/2 ∧ tR+L≤pH*I/2 ∧
      3*εcut*I^2*B^2+((Dcut:ℝ)+1)*I*B^2≤(ζcut*I*B)^2 := by
  let h₀:ℝ:=min (pmin/32) (href/8)
  let δcut:ℝ:=min δlimit (min (1/8) (pmin/32))
  let ζcut:ℝ:=min (pmin^2/256) (1/2)
  let εcut:ℝ:=min (ζcut^2/16) (pmin/16)
  let ζlimit:ℝ:=min (href/4) (min (pmin/16) (min (εcut*ω/8) (pmin*ω/16)))
  let εsmall:ℝ:=min (εcut/4) (pmin/16)
  have hh₀:0<h₀:=lt_min (by positivity) (by positivity)
  have hδ:0<δcut:=lt_min hδlimit (lt_min (by norm_num) (by positivity))
  have hδsmall:δcut<1/4:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hδcap:δcut≤δlimit:=min_le_left _ _
  have hζ:0<ζcut:=lt_min (by positivity) (by norm_num)
  have hε:0<εcut:=lt_min (by positivity) (by positivity)
  have hζlimit:0<ζlimit:=lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hεsmall:0<εsmall:=lt_min (by positivity) (by positivity)
  refine ⟨h₀,δcut,ζcut,εcut,ζlimit,εsmall,hh₀,hδ,hδsmall,hδcap,hζ,hε,hζlimit,hεsmall,?_⟩
  intro Dcut
  obtain ⟨N,hN⟩:=exists_nat_gt (((Dcut:ℝ)+1)/(ζcut^2/4))
  refine ⟨max N 1,by omega,?_⟩
  intro I B pH tR tH L h hNI hB0 hBI hpH htR0 htR htH0 htH hL0 hL hh0 hh
  have hI0:0≤I:=le_trans (by positivity) hNI
  have hNH:(N:ℝ)≤I:=by
    have hNmax:(N:ℝ)≤(max N 1:ℕ):=by exact_mod_cast (show N≤max N 1 by omega)
    exact hNmax.trans hNI
  have hsize:((Dcut:ℝ)+1)≤(ζcut^2/4)*I:=by
    have hh':((Dcut:ℝ)+1)<(N:ℝ)*(ζcut^2/4):=
      (div_lt_iff₀ (show 0<ζcut^2/4 by positivity)).mp hN
    have hh'':(N:ℝ)*(ζcut^2/4)≤I*(ζcut^2/4):=mul_le_mul_of_nonneg_right hNH (by positivity)
    nlinarith only [hh',hh'']
  have hδp:δcut≤pH/16:=by have hc:δcut≤pmin/32:=(min_le_right _ _).trans (min_le_right _ _);linarith
  have hpH0:0<pH:=hpmin.trans_le hpH
  have hpHsq:pmin^2≤pH^2:=by nlinarith [sq_nonneg (pH-pmin)]
  have hζp:ζcut≤pH^2/128:=by
    have hc:=min_le_left (pmin^2/256) (1/2:ℝ)
    dsimp [ζcut] at *
    nlinarith [sq_nonneg pmin]
  have hhp:2*h≤pH/8:=by have hc:=min_le_left (pmin/32) (href/8);dsimp [h₀] at *;linarith
  have hhref:2*h≤href-ζlimit:=by
    have hc:=min_le_right (pmin/32) (href/8)
    have hz:=min_le_left (href/4) (min (pmin/16) (min (εcut*ω/8) (pmin*ω/16)))
    dsimp [h₀,ζlimit] at *
    linarith
  have heSmallCut:εsmall≤εcut/4:=min_le_left _ _
  have heSmallP:εsmall≤pmin/16:=min_le_right _ _
  have hzCut:ζlimit≤εcut*ω/8:=by dsimp [ζlimit];exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hzPB:ζlimit≤pmin*ω/16:=by dsimp [ζlimit];exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzPI:ζlimit≤pmin/16:=by dsimp [ζlimit];exact (min_le_right _ _).trans (min_le_left _ _)
  have hLCut:L≤(εcut/8)*B:=by
    have h1:=mul_le_mul_of_nonneg_right hzCut hI0
    have h2:=mul_le_mul_of_nonneg_left hBI (show 0≤εcut/8 by positivity)
    nlinarith only [hL,h1,h2]
  have hLP:L≤(pmin/16)*B:=by
    have h1:=mul_le_mul_of_nonneg_right hzPB hI0
    have h2:=mul_le_mul_of_nonneg_left hBI (show 0≤pmin/16 by positivity)
    nlinarith only [hL,h1,h2]
  have hLPI:L≤(pmin/16)*I:=hL.trans (mul_le_mul_of_nonneg_right hzPI hI0)
  have htHCut:tH≤(εcut/4)*B:=htH.trans (mul_le_mul_of_nonneg_right heSmallCut hB0)
  have htHP:tH≤(pmin/16)*B:=htH.trans (mul_le_mul_of_nonneg_right heSmallP hB0)
  have htRP:tR≤(pmin/16)*I:=htR.trans (mul_le_mul_of_nonneg_right heSmallP hI0)
  have hCut:tH+2*L≤εcut*B:=by
    have hnon:=mul_nonneg hε.le hB0
    nlinarith only [htHCut,hLCut,hnon]
  have hCol:tH+L≤pH*B/2:=by
    have hp:=mul_le_mul_of_nonneg_right hpH hB0
    have hnon:=mul_nonneg hpmin.le hB0
    nlinarith only [htHP,hLP,hp,hnon]
  have hRow:tR+L≤pH*I/2:=by
    have hp:=mul_le_mul_of_nonneg_right hpH hI0
    have hnon:=mul_nonneg hpmin.le hI0
    nlinarith only [htRP,hLPI,hp,hnon]
  have hcoef:3*εcut≤ζcut^2/4:=by
    have hc:=min_le_left (ζcut^2/16) (pmin/16)
    dsimp [εcut] at *
    nlinarith [sq_nonneg ζcut]
  have hmult1:=mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg I) (sq_nonneg B))
  have hmult2:=mul_le_mul_of_nonneg_right hsize (mul_nonneg hI0 (sq_nonneg B))
  have hmatrix:3*εcut*I^2*B^2+((Dcut:ℝ)+1)*I*B^2≤(ζcut*I*B)^2:=by
    nlinarith only [hmult1,hmult2, sq_nonneg (ζcut*I*B)]
  exact ⟨hδp,hζp,hhp,hhref,hCut,hCol,hRow,hmatrix⟩
end Oberwolfach
