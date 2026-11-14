module

public import Oberwolfach.FirstVortexParentLevelToleranceAlignment

@[expose] public section
/-! A fixed configuration margin supports the smaller parent-event
configuration tolerance and the deeper record at once. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_configuration_alignment
    (r:ℕ) (βA cycleCoeff pathCoeff ζFixed δ:ℝ)
    (hδ:0≤δ) (hδfixed:2*δ≤ζFixed)
    (hcycle:3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*ζFixed)
    (hpath:3*βA≤pathCoeff-((r+4:ℕ):ℝ)*ζFixed):
    3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*δ ∧
    3*βA≤pathCoeff-((r+4:ℕ):ℝ)*δ ∧
    2*δ≤ζFixed ∧
    3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*ζFixed ∧
    3*βA≤pathCoeff-((r+4:ℕ):ℝ)*ζFixed :=by
  have hle:δ≤ζFixed:=by linarith
  have hcm:=mul_le_mul_of_nonneg_left hle (show (0:ℝ)≤(r+5:ℕ) by positivity)
  have hpm:=mul_le_mul_of_nonneg_left hle (show (0:ℝ)≤(r+4:ℕ) by positivity)
  exact ⟨by linarith,by linarith,hδfixed,hcycle,hpath⟩
end Oberwolfach
