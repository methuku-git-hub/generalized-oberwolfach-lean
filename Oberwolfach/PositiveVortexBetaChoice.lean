module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! The positive error required to construct a vortex is available for
every positive upper bound and reference tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem positive_vortex_beta_choice (βmax εref:ℝ) (hβ:0<βmax) (hε:0<εref):
    ∃ β:ℝ,0<β ∧ β≤βmax ∧ β≤εref/4:=by
  let β:=min βmax (εref/4)
  refine ⟨β,lt_min hβ (by positivity),min_le_left _ _,min_le_right _ _⟩
end Oberwolfach
