module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The canonical centres satisfy the exact sampled-density identities. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_adaptive_canonical_centre (ρ s₀ B:ℝ) (hρ:0<ρ):
    (ρ*s₀/2)*(2*B/ρ)=s₀*B := by
  field_simp

theorem marked_adaptive_canonical_load (ρ s₀ H:ℝ) (hρ:0<ρ):
    H*s₀=(2*H/ρ)*(ρ*s₀/2) := by
  field_simp
end Oberwolfach
