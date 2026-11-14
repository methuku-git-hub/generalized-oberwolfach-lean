module

public import Oberwolfach.OrdinaryTriangleOriginalChoicesBeforeFailure
public import Oberwolfach.OrdinaryOriginalTriangleParentReferenceChoices
public import Oberwolfach.OrdinaryOriginalPreSampleCorrectionChoices

@[expose] public section
/-! Choose the triangle fine-cover cap before the original matching,
correction and contraction parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_presample_choices
    (L:ℕ) (βfreq ρ₀ α capEdit θhost ηcap:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hcap:0<capEdit) (hθhost:(1/2:ℝ)≤θhost) (hηcap:0<ηcap)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold 3)+(α/2)/2≤1):
    let smin:=βfreq/200;let pstar:=ρ₀*smin/2;let ω:=ρ₀/4;
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ 0<c ∧ 0<C ∧ OrdinaryTriangleHubEarlyBeforeFailure (α/2) ρ₀ pstar κ c C ∧
    ∃δAbs h εabs εv:ℝ,
      OrdinaryWeightedCorrectionAfterEarly 3 (α/2) pstar ω δAbs h εabs εv ∧
      let εmax:=min κ (min (ρ₀/16) (1/8:ℝ));
      let capInner:=min εmax (min εabs εv);
      0<capInner ∧ capInner≤κ ∧ capInner≤ρ₀/16 ∧ capInner≤1/8 ∧
      capInner≤εabs ∧ capInner≤εv ∧
      OrdinaryOriginalPreSampleJointShape L 3 βfreq ρ₀ α (α/2) capInner capEdit θhost
        (by omega) hβ hβ1 hρ hα ∧
      ∃ηP:ℝ,0<ηP ∧ ηP≤ηcap ∧ ∀d:ℕ,∀hd:2≤d,
        OrdinaryTriangleParentReferenceChoices d hd (α/2) ρ₀ pstar ηP (by positivity) (by positivity) :=by
  intro smin pstar ω
  obtain ⟨κ,c,C,hκ,hκ1,hc,hC,htri,δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,hPre⟩:=
    ordinary_triangle_original_choices_before_failure L βfreq ρ₀ α capEdit θhost hβ hβ1 hρ hρ1 hα hcap hθhost
  let ηP:=min α ηcap/2
  have hη:0<ηP:=by dsimp [ηP];positivity
  have hηcap':ηP≤ηcap:=by dsimp [ηP];have hh:=min_le_right α ηcap;linarith
  have hparents:=ordinary_original_triangle_parent_reference_choices βfreq ρ₀ α ηP hβ hβ1 hρ hρ1 hα hη hmargin
  exact ⟨κ,c,C,hκ,hκ1,hc,hC,htri,δAbs,h,εabs,εv,hCorr,hInner,hA,hR,h8,hAbs,hV,hPre,ηP,hη,hηcap',hparents⟩
end Oberwolfach
