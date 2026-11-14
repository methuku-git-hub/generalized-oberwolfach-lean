module

public import Oberwolfach.RetentionRestrictionLocalEvent

@[expose] public section
/-! The local retention tolerance is selected after the global one and can
be made smaller than any later positive level tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_restriction_local_mono_tolerance
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (A:Finset V) (H:Finset U) (ζ₁ ζ₂:ℝ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (hζ:ζ₁≤ζ₂) (hgood:RetainedRestrictionLocalGood π d σ g t A H ζ₁ J):
    RetainedRestrictionLocalGood π d σ g t A H ζ₂ J :=by
  constructor
  · intro u hu
    exact (hgood.1 u hu).trans (mul_le_mul_of_nonneg_right hζ (by positivity))
  · intro v hv
    exact (hgood.2 v hv).trans (mul_le_mul_of_nonneg_right hζ (by positivity))

theorem first_vortex_selector_local_retention_choice
    (ζret upper:ℝ) (hret:0<ζret) (hupper:0<upper):
    ∃ζlocal:ℝ,0<ζlocal ∧ ζlocal≤ζret ∧ ζlocal≤upper ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
      (A:Finset V) (H:Finset U) (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      RetainedRestrictionLocalGood π d σ g t A H ζlocal J→
      RetainedRestrictionLocalGood π d σ g t A H ζret J :=by
  let ζlocal:=min ζret upper/2
  have hlocal:0<ζlocal:=by dsimp [ζlocal]; positivity
  have hret':ζlocal≤ζret:=by dsimp [ζlocal];have :=min_le_left ζret upper;linarith
  have hupper':ζlocal≤upper:=by dsimp [ζlocal];have :=min_le_right ζret upper;linarith
  refine ⟨ζlocal,hlocal,hret',hupper',?_⟩
  intro V U Γ Color _ _ _ _ _ _ π d σ g t A H J hgood
  exact retained_restriction_local_mono_tolerance π d σ g t A H ζlocal ζret J hret' hgood
end Oberwolfach
