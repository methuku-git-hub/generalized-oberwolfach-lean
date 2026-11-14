module

public import Oberwolfach.OrdinaryDeepRowsCutsEarlyChoiceBeforeLoad
public import Oberwolfach.OrdinaryOriginalPreSampleCorrectionChoices

@[expose] public section
/-! For reserved cycles of length at least four, select the deep wheel
constants before the ordinary selector, correction and vortex contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_original_choices_before_load
    (L rstar:ℕ) (βfreq ρ₀ α capEdit θhost:ℝ)
    (hr:4≤rstar) (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hcap:0<capEdit) (hθhost:(1/2:ℝ)≤θhost):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    let αcut:=min (α/8) (1/4:ℝ);
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃Kdeep:ℕ,0<Kdeep ∧ ∃aDeep ε₀ ρdeep θdeep:ℝ,
      0<aDeep ∧ 0<ε₀ ∧ 0<ρdeep ∧ 0<θdeep ∧
      OrdinaryDeepRowsCutsEarlyBeforeLoad (rstar-1) Kdeep (α/2) ρ₀ pstar αcut c C aDeep ε₀ ρdeep θdeep ∧
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly rstar (α/2) pstar ω δAbs h εabs εv ∧
      let εmax:=min aDeep (min (ρ₀/16) (1/8:ℝ));
      let capInner:=min εmax (min εabs εv);
      0<capInner ∧ capInner≤aDeep ∧ capInner≤ρ₀/16 ∧ capInner≤1/8 ∧
      capInner≤εabs ∧ capInner≤εv ∧
      OrdinaryOriginalPreSampleJointShape L rstar βfreq ρ₀ α (α/2) capInner capEdit θhost
        (by omega) hβ hβ1 hρ hα :=by
  intro smin pstar ω αcut
  have hs:0<smin:=by dsimp [smin]; positivity
  have hs1:smin≤1:=by dsimp [smin]; linarith
  have hp:0<pstar:=by dsimp [pstar]; positivity
  have hp1:pstar≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hρ1 hs.le
    have hmul:ρ₀*smin≤1:=by nlinarith [hh,hs1]
    dsimp [pstar]
    nlinarith
  have hc:0<αcut:=by dsimp [αcut]; positivity
  have hc1:αcut≤1/2:=by dsimp [αcut]; exact le_trans (min_le_right _ _) (by norm_num)
  have hcα:αcut≤(α/2)/2:=by dsimp [αcut]; have hh:=min_le_left (α/8) (1/4:ℝ); linarith
  obtain ⟨c,C,hc0,hC0,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε₀,hρdeep,hθdeep,hdeep⟩:=
    ordinary_deep_rows_cuts_early_choice_before_load (rstar-1) (by omega) (α/2) ρ₀ pstar αcut
      (by positivity) hρ hp hp1 hc hc1 hcα
  let εmax:=min aDeep (min (ρ₀/16) (1/8:ℝ))
  have hmax:0<εmax:=by dsimp [εmax]; positivity
  obtain ⟨δAbs,h,εabs,εv,hCorr,hInner,hMax,hAbs,hV,hPre⟩:=
    ordinary_original_presample_correction_choices L rstar βfreq ρ₀ α εmax capEdit θhost
      (by omega) hβ hβ1 hρ hρ1 hα hmax hcap hθhost
  have hA:εmax≤aDeep:=min_le_left _ _
  have hR:εmax≤ρ₀/16:=le_trans (min_le_right _ _) (min_le_left _ _)
  have h8:εmax≤1/8:=le_trans (min_le_right _ _) (min_le_right _ _)
  exact ⟨c,C,hc0,hC0,Kdeep,hK,aDeep,ε₀,ρdeep,θdeep,ha,hε₀,hρdeep,hθdeep,hdeep,
    δAbs,h,εabs,εv,hCorr,hInner,le_trans hMax hA,le_trans hMax hR,le_trans hMax h8,hAbs,hV,hPre⟩
end Oberwolfach
