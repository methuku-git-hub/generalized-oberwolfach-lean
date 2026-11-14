module

public import Oberwolfach.FirstVortexSpacingClassRetentionChoices

@[expose] public section
/-! Choose one spacing and class cutoff for the selector, the all-hub
boundary rate, and the active-spoke budget; then shrink retention as needed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_spacing_all_budgets (r:ℕ) (θ b active upper:ℝ)
    (hθ:0<θ) (hb:0<b) (hactive:0<active) (hupper:0<upper):
    ∃d K:ℕ,3≤d ∧ (r+4)+2≤d ∧ 3≤K ∧
      4/(d:ℝ)<b ∧ 1/(d:ℝ)≤active ∧ 1/(d:ℝ)≤θ/1024 ∧
      (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
      5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∃ζret:ℝ,0<ζret ∧ ζret≤upper ∧ ζret≤θ/4096 ∧ ∃Nret:ℕ,
      ∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n :=by
  obtain ⟨D,hD⟩:=exists_nat_gt (max (4/b) (1/active))
  obtain ⟨d,K,hd,hdMin,hdlarge,hK,hspace,hcut,hhost,ζold,hζold,hζθ,Nret,hNret⟩:=
    first_vortex_spacing_class_retention_choices r (D+1) θ hθ
  have hdpos:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hDn:(D:ℝ)<d:=by exact_mod_cast (show D<d by omega)
  have hbdiv:4/b<(d:ℝ):=lt_of_le_of_lt (le_max_left _ _) (lt_trans hD hDn)
  have hadiv:1/active<(d:ℝ):=lt_of_le_of_lt (le_max_right _ _) (lt_trans hD hDn)
  have hbspace:4/(d:ℝ)<b:=by
    have hh:4<(d:ℝ)*b:=(div_lt_iff₀ hb).mp hbdiv
    apply (div_lt_iff₀ hdpos).2
    nlinarith
  have haspace:1/(d:ℝ)≤active:=by
    have hh:1<(d:ℝ)*active:=(div_lt_iff₀ hactive).mp hadiv
    apply (div_le_iff₀ hdpos).2
    nlinarith
  let ζret:=min ζold (upper/2)
  have hζ:0<ζret:=by dsimp [ζret];positivity
  have hζold':ζret≤ζold:=min_le_left _ _
  have hζupper:ζret≤upper:=by dsimp [ζret];have hh:=min_le_right ζold (upper/2);linarith
  refine ⟨d,K,hd,hdlarge,hK,hbspace,haspace,hspace,hcut,hhost,ζret,hζ,hζupper,hζold'.trans hζθ,Nret,?_⟩
  intro n hn q err hq herr
  have hh:=hNret n hn q err hq herr
  have hmul:=mul_le_mul_of_nonneg_right hζold' (show (0:ℝ)≤n by positivity)
  have hcoeff:0≤(((((r+4)+1)*d-1:ℕ):ℝ)):=by positivity
  have hterm:=mul_le_mul_of_nonneg_left (show 2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n≤
    2*((n:ℝ)^(3/4:ℝ)/d)+ζold*n by linarith) hcoeff
  linarith
end Oberwolfach
