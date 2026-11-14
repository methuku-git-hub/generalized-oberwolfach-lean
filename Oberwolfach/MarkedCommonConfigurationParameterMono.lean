module

public import Oberwolfach.MarkedCommonConfigurationSpokeChanges

@[expose] public section
/-! Weakening the common-configuration coefficient and enlarging its error. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_configuration_parameter_mono
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (β₀ ζ₀ β₁ ζ₁:ℝ) (hβ:β₁≤β₀) (hζ:ζ₀≤ζ₁)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hc:MarkedCommonConfigurationsWithSpokes r P π d β₀ ζ₀ σ H):
    MarkedCommonConfigurationsWithSpokes r P π d β₁ ζ₁ σ H:=by
  have hmul5:0≤((r+5:ℕ):ℝ)*(ζ₁-ζ₀):=mul_nonneg (by positivity) (sub_nonneg.mpr hζ)
  have hmul4:0≤((r+4:ℕ):ℝ)*(ζ₁-ζ₀):=mul_nonneg (by positivity) (sub_nonneg.mpr hζ)
  have h1:32*β₁-(r+5:ℕ)*ζ₁≤32*β₀-(r+5:ℕ)*ζ₀:=by nlinarith
  have h2:16*β₁-2*(r+5:ℕ)*ζ₁≤16*β₀-2*(r+5:ℕ)*ζ₀:=by nlinarith
  have h3:16*β₁-2*(r+4:ℕ)*ζ₁≤16*β₀-2*(r+4:ℕ)*ζ₀:=by nlinarith
  refine ⟨?_,?_,?_⟩
  · intro C hC
    exact (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)).trans (hc.1 C hC)
  · intro u hu
    exact (mul_le_mul_of_nonneg_right h2 (by positivity)).trans (hc.2.1 u hu)
  · intro v v' hv u hu j
    exact (mul_le_mul_of_nonneg_right h3 (by positivity)).trans (hc.2.2 v v' hv u hu j)
end Oberwolfach
