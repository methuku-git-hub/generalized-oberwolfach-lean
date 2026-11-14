module

public import Mathlib.Tactic

@[expose] public section
/-! Fix the packing margin before choosing the reference edit and cleanup
losses. All later choices retain a positive portion of the cut margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_reference_packing_margin (h:ℝ) (hh:0<h):
    ∃hpack:ℝ,0<hpack ∧ ∀ζroot ξ ζ:ℝ,
      ζroot≤h→ξ+ζ≤h/2→hpack≤(2*h-ζroot)-ξ-ζ :=by
  refine ⟨h/4,by positivity,?_⟩
  intro ζroot ξ ζ hroot hloss
  linarith
end Oberwolfach
