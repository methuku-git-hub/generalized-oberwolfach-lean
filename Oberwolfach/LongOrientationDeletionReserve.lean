module

public import Oberwolfach.LongOrientationDeletionScale

@[expose] public section
/-! Leave half of the matching deletion budget for a separate protected
or previously used physical graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_orientation_deletion_scale_with_reserve
    (Δ C ξmax:ℝ) (hΔ:0<Δ) (hC:0≤C) (hmax:0<ξmax):
    ∃ ξcap:ℝ,0<ξcap ∧ ξcap≤ξmax ∧ ∃ N:ℕ,
      ∀n≥N,∀ ξ η:ℝ,0≤ξ→ξ≤ξcap→η≤Δ/2→
        η+ξ+C*Real.sqrt ξ+5*(n:ℝ)^(-(1/5:ℝ))≤Δ := by
  obtain ⟨ξcap,hξ,hcap,N,hN⟩:=long_orientation_deletion_scale (Δ/2) C ξmax (by positivity) hC hmax
  refine ⟨ξcap,hξ,hcap,N,?_⟩
  intro n hn ξ η hξ0 hξcap hη
  have h:=hN n hn ξ hξ0 hξcap
  linarith
end Oberwolfach
