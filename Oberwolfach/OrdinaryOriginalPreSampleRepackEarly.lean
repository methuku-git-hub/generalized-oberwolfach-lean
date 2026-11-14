module

public import Oberwolfach.OrdinaryOriginalPreSampleAtEarly

@[expose] public section
/-! Recover the original matching selector at the same spacing from its
preserved early parameters and later edit-cap continuation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_original_presample_repack_early
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace ε:ℝ)
    (hAt:OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k)
    (hEarly:OrdinaryPlacementEarlyRateData γList ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace ε dMin)
    (hTail:OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace ε):
    OrdinaryOriginalPreSampleJointAtSpacing L rstar d βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα :=by
  exact ⟨m,k,βPlace,lamPlace,ζPlace,ε,dMin,hAt,hEarly,hTail⟩
end Oberwolfach
