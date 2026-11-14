module

public import Oberwolfach.OrdinaryOriginalPreSampleAtEarly

@[expose] public section
/-! Choose the matching placement only after the certificate tolerance is
known, retaining the early vortex and list parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_presample_for_certificate_cap
    (L rstar m k dMin:ℕ) (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (capOriginal ηedit:ℝ) (hcap:0<capOriginal) (hη:0<ηedit):
    ∃capChosen:ℝ,0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηedit ∧
      ∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capChosen θhost
          hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly :=by
  let capChosen:=min capOriginal ηedit
  have hChosen:0<capChosen:=by dsimp [capChosen]; positivity
  exact ⟨capChosen,hChosen,min_le_left _ _,min_le_right _ _,hTail capChosen hChosen⟩
end Oberwolfach
