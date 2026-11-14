module

public import Oberwolfach.MarkedInnerDomainPackingNumerics

@[expose] public section

/-! The all-root extension event has a p^3 lower bound, rather than the
p^2 bound available for particular configurations. The explicit free-use
scale p^4 still covers a p^9 remainder and is small enough for that bound.
All tolerances are fixed before the permutation separation radius. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_boundary_cover_scale_choices (l:ℕ) (β ν:ℝ) (hβ:0<β) (hν:0<ν):
    ∃ p₀:ℝ,0<p₀∧∀ p:ℝ,0<p→p≤p₀→
      (p≤1)∧(p^4≤1)∧(100*((l:ℝ)+20)*p^4≤p^3*β/2)∧
      (p^9≤(p^4)^2)∧
      ((30+3*((l:ℝ)+5))*p^4≤p^3)∧
      ((30+3*((l:ℝ)+5))*p^4≤ν*p^3):=by
  let C:ℝ:=30+3*((l:ℝ)+5)
  have hC:0<C:=by dsimp [C];positivity
  let p₀:=min 1 (min (β/(200*((l:ℝ)+20))) (min (1/C) (ν/C)))
  have hp₀:0<p₀:=lt_min (by norm_num) (lt_min (div_pos hβ (by positivity))
    (lt_min (one_div_pos.mpr hC) (div_pos hν hC)))
  refine ⟨p₀,hp₀,?_⟩
  intro p hp hsmall
  have hp1:p≤1:=hsmall.trans (min_le_left _ _)
  have hβp:p≤β/(200*((l:ℝ)+20)):=hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hCp:p≤1/C:=hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνp:p≤ν/C:=hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsc:100*((l:ℝ)+20)*p≤β/2:=by
    have h:=(le_div_iff₀ (by positivity : (0:ℝ)<200*((l:ℝ)+20))).mp hβp
    linarith only [h]
  have hc:C*p≤1:=by have h:=(le_div_iff₀ hC).mp hCp;linarith only [h]
  have hv:C*p≤ν:=by have h:=(le_div_iff₀ hC).mp hνp;linarith only [h]
  refine ⟨hp1,pow_le_one₀ hp.le hp1,?_,?_,?_,?_⟩
  · have h:=mul_le_mul_of_nonneg_right hsc (pow_nonneg hp.le 3)
    nlinarith only [h]
  · have h:=pow_le_pow_of_le_one hp.le hp1 (by omega : 8≤9)
    nlinarith only [h]
  · have h:=mul_le_mul_of_nonneg_right hc (pow_nonneg hp.le 3)
    dsimp only [C] at h
    nlinarith only [h]
  · have h:=mul_le_mul_of_nonneg_right hv (pow_nonneg hp.le 3)
    dsimp only [C] at h
    nlinarith only [h]
end Oberwolfach
