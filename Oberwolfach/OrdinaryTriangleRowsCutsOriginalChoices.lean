module

public import Oberwolfach.OrdinaryTriangleRowsCutsChooseEarly
public import Oberwolfach.OrdinaryOriginalPreSampleCorrectionChoices

@[expose] public section
/-! Choose the triangle fine-cover cap before the original matching,
correction and contraction parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_rows_cuts_original_choices
    (L:ℕ) (βfreq ρ₀ α capEdit θhost:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hcap:0<capEdit) (hθhost:(1/2:ℝ)≤θhost):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    ∃κ:ℝ,0<κ ∧ κ≤1 ∧ OrdinaryTriangleRowsCutsAfterEarly (α/2) ρ₀ pstar κ ∧
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly 3 (α/2) pstar ω δAbs h εabs εv ∧
      let εmax:=min κ (min (ρ₀/16) (1/8:ℝ));
      let capInner:=min εmax (min εabs εv);
      0<capInner ∧ capInner≤κ ∧ capInner≤ρ₀/16 ∧ capInner≤1/8 ∧
      capInner≤εabs ∧ capInner≤εv ∧
      OrdinaryOriginalPreSampleJointShape L 3 βfreq ρ₀ α (α/2) capInner capEdit θhost
        (by omega) hβ hβ1 hρ hα :=by
  intro smin pstar ω
  have hs:0<smin:=by dsimp [smin]; positivity
  have hs1:smin≤1:=by dsimp [smin]; linarith
  have hp:0<pstar:=by dsimp [pstar]; positivity
  have hp1:pstar≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hρ1 hs.le
    have hmul:ρ₀*smin≤1:=by nlinarith [hh,hs1]
    dsimp [pstar]
    nlinarith
  obtain ⟨κ,hκ,hκ1,_,htri⟩:=ordinary_triangle_rows_cuts_choose_early (α/2) ρ₀ pstar 1
    (by positivity) hρ hp hp1 (by norm_num)
  let εmax:=min κ (min (ρ₀/16) (1/8:ℝ))
  have hmax:0<εmax:=by dsimp [εmax]; positivity
  obtain ⟨δAbs,h,εabs,εv,hCorr,hInner,hMax,hAbs,hV,hPre⟩:=
    ordinary_original_presample_correction_choices L 3 βfreq ρ₀ α εmax capEdit θhost
      (by omega) hβ hβ1 hρ hρ1 hα hmax hcap hθhost
  have hA:εmax≤κ:=min_le_left _ _
  have hR:εmax≤ρ₀/16:=le_trans (min_le_right _ _) (min_le_left _ _)
  have h8:εmax≤1/8:=le_trans (min_le_right _ _) (min_le_right _ _)
  exact ⟨κ,hκ,hκ1,htri,δAbs,h,εabs,εv,hCorr,hInner,
    le_trans hMax hA,le_trans hMax hR,le_trans hMax h8,hAbs,hV,hPre⟩
end Oberwolfach
