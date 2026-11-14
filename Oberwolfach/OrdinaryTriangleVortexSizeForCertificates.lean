module

public import Oberwolfach.OrdinaryLookbackVortexThresholdPayload
public import Oberwolfach.OrdinaryParentVortexSizeChoice

@[expose] public section
/-! Choose one actual lookback-vortex size after the selected event and
certificate thresholds, and before the absorber support size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_vortex_size_for_certificates
    (β ε ρ₀:ℝ) (d M vCommon Mhost Mcut:ℕ)
    (hβ:0<β) (hε:0<ε) (hεsmall:ε<1/4) (hρ:0<ρ₀):
    ∃mVortex mv:ℕ,1≤mv ∧ vCommon≤mv ∧ mVortex≤mv ∧
      (M:ℝ)≤ε*mv/2 ∧ (Mhost:ℝ)≤ε*mv/2 ∧ (Mcut:ℝ)≤ε*mv/2 ∧
      OrdinaryLookbackVortexAt β ε ρ₀ d mVortex :=by
  obtain ⟨mVortex,_,hvortex⟩:=vortex_lookback_with_permutation_exists hβ hε hεsmall hρ 2 (2*d+1) (by omega)
  have hlook:OrdinaryLookbackVortexAt β ε ρ₀ d mVortex:=by
    intro V U _ _ P D mv hreg hhalf hρlo hρhi hm hmn
    exact hvortex V U P D mv hreg hhalf hρlo hρhi hm hmn
  obtain ⟨mv,hmv,hCommon,hVortex,hmax,hcut⟩:=
    ordinary_parent_vortex_size_choice ε hε vCommon mVortex (max M Mhost) Mcut
  have hM:(M:ℝ)≤(max M Mhost:ℕ):=by exact_mod_cast (le_max_left M Mhost)
  have hHost:(Mhost:ℝ)≤(max M Mhost:ℕ):=by exact_mod_cast (le_max_right M Mhost)
  exact ⟨mVortex,mv,hmv,hCommon,hVortex,hM.trans hmax,hHost.trans hmax,hcut,hlook⟩
end Oberwolfach
