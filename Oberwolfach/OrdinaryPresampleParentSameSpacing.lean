module

public import Oberwolfach.OrdinaryOriginalPreSampleJointAtSpacing
public import Oberwolfach.OrdinaryParentReferenceCompatibleChoices

@[expose] public section
/-! Use the spacing selected by the original matching construction in the
parent reference construction as well. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_presample_parent_same_spacing
    (L rstar loadK:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:4≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (hpre:OrdinaryOriginalPreSampleJointShape L rstar βfreq ρ₀ α γList capInner capEdit θhost (by omega) hβfreq hβ1 hρ₀ hα)
    (αparent pstar ηP:ℝ) (hp:0<pstar)
    (hparents:∀d:ℕ,∀hd:2≤d,OrdinaryParentReferenceCompatibleChoices (rstar-1) loadK d (by omega) hd αparent ρ₀ pstar ηP hp):
    ∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleJointAtSpacing L rstar d βfreq ρ₀ α γList capInner capEdit θhost (by omega) hβfreq hβ1 hρ₀ hα ∧
      OrdinaryParentReferenceCompatibleChoices (rstar-1) loadK d (by omega) hd αparent ρ₀ pstar ηP hp :=by
  obtain ⟨d,hd,hpre⟩:=ordinary_original_presample_choose_spacing L rstar βfreq ρ₀ α γList capInner capEdit θhost
    (by omega) hβfreq hβ1 hρ₀ hα hpre
  exact ⟨d,hd,hpre,hparents d hd⟩
end Oberwolfach
