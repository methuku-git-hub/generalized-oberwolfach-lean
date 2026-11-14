module

public import Oberwolfach.LongCompatibleLargeSpacingChoices
public import Oberwolfach.ResidualLongErrorBudgetBelow

@[expose] public section
/-! Choose spacing, the class cutoff and the retention error before any
later matching tolerance, with the exact bounds used by the host caller. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_spacing_class_retention_choices
    (r dMin:ℕ) (θ:ℝ) (hθ:0<θ):
    ∃d K:ℕ, 3≤d ∧ dMin≤d ∧ (r+4)+2≤d ∧ 3≤K ∧
      1/(d:ℝ)≤θ/1024 ∧
      (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
      5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∃ζret:ℝ,0<ζret ∧ ζret≤θ/4096 ∧ ∃Nret:ℕ,
      ∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n:=by
  obtain ⟨d,hd3,hdMin,hspacing,hcut,_,hchoice⟩:=
    long_compatible_large_spacing_choices (r+4) (max dMin ((r+4)+2)) θ 1 hθ (by norm_num)
  have hdMin':dMin≤d:=(le_max_left _ _).trans hdMin
  have hdlarge:(r+4)+2≤d:=(le_max_right _ _).trans hdMin
  obtain ⟨D,hD⟩:=exists_nat_gt (4*((((r+4):ℕ):ℝ)+1)*(d:ℝ)/θ)
  let K:=max D 3
  have hK:3≤K:=le_max_right _ _
  have hKlarge:4*((((r+4):ℕ):ℝ)+1)*(d:ℝ)/θ≤K:=
    le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (le_max_left D 3)))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hfloor⟩:=hchoice K hK
  have hcut':1/(((((r+4):ℕ):ℝ)+1)*(d:ℝ))≤θ:=by
    convert hcut using 1 <;> field_simp
  obtain ⟨ζret,hζ,hζbound,Nret,hNret⟩:=
    residual_long_error_budget_below (r+4) d (by omega) (by omega) θ (θ/4096) hθ (by positivity) hcut'
  exact ⟨d,K,hd3,hdMin',hdlarge,hK,hspacing,hcut,hfloor hKlarge,ζret,hζ,hζbound,Nret,hNret⟩
end Oberwolfach
