module

public import Oberwolfach.LongOrientationDeletionReserve

@[expose] public section
/-! Split the fixed raw list coefficient between the final extending margin,
the inner-set and trimming losses, and later physical deletions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_list_budget_alignment
    (β εcap ηcap ζcap:ℝ) (hβ:0<β) (hε:0<εcap) (hη:0<ηcap) (hζ:0<ζcap):
    ∃lam ε η ζ:ℝ,0<lam ∧ 0<ε ∧ ε≤εcap ∧ 0<η ∧ η≤ηcap ∧ 0<ζ ∧ ζ≤ζcap ∧
      β/2+ε+β/16+η≤lam ∧ lam+2*ζ≤β := by
  refine ⟨3*β/4,min εcap (β/32),min ηcap (β/32),min ζcap (β/16),by positivity,
    by positivity,min_le_left _ _,by positivity,min_le_left _ _,by positivity,min_le_left _ _,?_,?_⟩
  · have he:=min_le_right εcap (β/32)
    have hh:=min_le_right ηcap (β/32)
    linarith
  · have hz:=min_le_right ζcap (β/16)
    linarith
end Oberwolfach
