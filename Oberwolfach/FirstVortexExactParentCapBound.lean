module

public import Oberwolfach.MarkedVortexFixedMarginLocalCorrectionCap

@[expose] public section
/-! The chosen global cap is below the exact transfer threshold for the
actual early parent density and weight parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def FirstVortexExactParentCapBound
    (r:ℕ) (α ρ₀ κ ζCfg thetaDeep BA cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀):Prop :=
    let t₀:=1/(200*((r+4:ℕ):ℝ))
    let p0:=ρ₀/(800*((r+4:ℕ):ℝ));
    ∃hk:0<κ,∃hz:0<ζCfg,∃ht:0<thetaDeep,∃hB:0≤BA,
      cap≤Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ (2*α) (ρ₀/4) p0 p0 t₀ p0 ζCfg thetaDeep (1:ℝ)
        BA p0 (1:ℝ) (1:ℝ) (1:ℝ) hk (by positivity) (by positivity) (by dsimp [p0];positivity) (by dsimp [p0];positivity)
        (by dsimp [t₀];positivity) hz ht (by norm_num) hB (by dsimp [p0];positivity) (by norm_num) (by norm_num) (by norm_num))
end Oberwolfach
