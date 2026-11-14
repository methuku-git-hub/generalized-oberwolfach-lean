module

public import Mathlib.Tactic

@[expose] public section
/-! Choose local edit scales for an arbitrary fixed wheel length; the
    threshold absorbs additive constants depending on that length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_general_parent_edit_scale_choice
    (r:ℕ) (βH ηH B ω pstar ζcap:ℝ)
    (hβH:0<βH) (hηH:0<ηH) (hB:0≤B) (hω:0<ω) (hp:0<pstar) (hcap:0<ζcap):
    ∃βparent εparent ζ rate:ℝ,0<βparent ∧ 0<εparent ∧ 0<ζ ∧ 0<rate ∧
      ζ≤ζcap ∧ βparent+ζ≤βH ∧
    ∃N₀:ℕ,1≤N₀ ∧ ∀N U L:ℝ,(N₀:ℝ)≤N→ω*N≤U→0≤L→L≤rate*N→
      L≤ζ*N ∧ L≤ζ*U ∧
      8*(L+1)≤(βH-βparent)*N ∧
      5*(r:ℝ)^4*(L+1)≤(βH-βparent)*N ∧
      ηH+8*(r:ℝ)^4*(B/(ω*pstar^(2*r-1)))*L/N≤εparent :=by
  let C:ℝ:=8*(r:ℝ)^4*(B/(ω*pstar^(2*r-1)))
  let C₀:ℝ:=8+5*(r:ℝ)^4
  have hC:0≤C:=by dsimp [C];positivity
  have hC₀:0<C₀:=by dsimp [C₀];positivity
  have hC8:8≤C₀:=by
    dsimp [C₀]
    have hh:0≤5*(r:ℝ)^4:=by positivity
    linarith
  have hCr:5*(r:ℝ)^4≤C₀:=by dsimp [C₀];linarith
  let ζ:ℝ:=min (ζcap/2) (min (βH/4) (ηH/(2*(C+1))))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  let rate:ℝ:=min (ζ*(min (1:ℝ) ω)/2) (min (βH/(8*C₀)) (ηH/(2*(C+1))))
  have hrate:0<rate:=by dsimp [rate];positivity
  obtain ⟨N₀,hN₀⟩:=exists_nat_gt (8*C₀/βH)
  refine ⟨βH/2,2*ηH,ζ,rate,by positivity,by positivity,hζ,hrate,?_,?_,max N₀ 1,by omega,?_⟩
  · have hh:=min_le_left (ζcap/2) (min (βH/4) (ηH/(2*(C+1))))
    dsimp [ζ];linarith
  · have hh:ζ≤βH/4:=le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  intro N U L hN hU hL hLrate
  have hN0:(N₀:ℝ)≤N:=by
    have hh:(N₀:ℝ)≤(max N₀ 1:ℕ):=by exact_mod_cast (show N₀≤max N₀ 1 by omega)
    exact hh.trans hN
  have hNlarge:8*C₀/βH<N:=hN₀.trans_le hN0
  have hNpos:0<N:=(show 0<8*C₀/βH by positivity).trans hNlarge
  have hmin0:0<min (1:ℝ) ω:=lt_min (by norm_num) hω
  have hmin1:min (1:ℝ) ω≤1:=min_le_left _ _
  have hminω:min (1:ℝ) ω≤ω:=min_le_right _ _
  have hrateζ:rate≤ζ*(min (1:ℝ) ω)/2:=min_le_left _ _
  have hrateβ:rate≤βH/(8*C₀):=le_trans (min_le_right _ _) (min_le_left _ _)
  have hrateη:rate≤ηH/(2*(C+1)):=le_trans (min_le_right _ _) (min_le_right _ _)
  have hNβ:8*C₀<βH*N:=by simpa only [mul_comm] using (div_lt_iff₀ hβH).mp hNlarge
  have hLζ:L≤ζ*N:=by
    have hh:=mul_le_mul_of_nonneg_left hmin1 hζ.le
    have hcap:rate≤ζ:=by nlinarith only [hrateζ,hh,hζ]
    exact hLrate.trans (mul_le_mul_of_nonneg_right hcap hNpos.le)
  have hLζU:L≤ζ*U:=by
    have hh:=mul_le_mul_of_nonneg_left hminω hζ.le
    have hcap:rate≤ζ*ω:=by nlinarith only [hrateζ,hh,hζ,hω]
    have hh':=mul_le_mul_of_nonneg_left hU hζ.le
    have hh'':=hLrate.trans (mul_le_mul_of_nonneg_right hcap hNpos.le)
    nlinarith only [hh',hh'']
  have hLβ:L≤(βH/(8*C₀))*N:=hLrate.trans (mul_le_mul_of_nonneg_right hrateβ hNpos.le)
  have hCL:C₀*L≤βH*N/8:=by
    have hh:=mul_le_mul_of_nonneg_left hLβ hC₀.le
    have heq:C₀*((βH/(8*C₀))*N)=βH*N/8:=by field_simp <;> ring
    rw [heq] at hh
    exact hh
  have hCtotal:C₀*(L+1)≤(βH-βH/2)*N:=by nlinarith only [hCL,hNβ,hC₀]
  have hLη:L≤(ηH/(2*(C+1)))*N:=hLrate.trans (mul_le_mul_of_nonneg_right hrateη hNpos.le)
  refine ⟨hLζ,hLζU,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right hC8 (by linarith)).trans hCtotal
  · exact (mul_le_mul_of_nonneg_right hCr (by linarith)).trans hCtotal
  · have hden:0<2*(C+1):=by positivity
    have hrateC:C*(ηH/(2*(C+1)))≤ηH:=by
      have heq:C*(ηH/(2*(C+1)))=C*ηH/(2*(C+1)):=by ring
      rw [heq]
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hC hηH.le]
    have hCN:C*L/N≤ηH:=by
      apply (div_le_iff₀ hNpos).2
      have hh:=mul_le_mul_of_nonneg_left hLη hC
      have hh':=mul_le_mul_of_nonneg_right hrateC hNpos.le
      nlinarith only [hh,hh']
    dsimp only [C] at hCN
    linarith only [hCN]
end Oberwolfach
