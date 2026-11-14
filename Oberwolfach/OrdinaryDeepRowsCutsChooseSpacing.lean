module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterSpacing

@[expose] public section
/-! Choose the terminal vortex size after the spacing and errors, before the
host and sampled configuration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_rows_cuts_choose_spacing
    (m K:ℕ) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap:ℝ)
    (hdeep:OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap)
    (d:ℕ) (hd:2≤d) (β:ℝ) (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hβε:β≤ε₀) (hgap:ξ+2*β<ηHub):
    ∃v₀:ℕ,1≤v₀ ∧ OrdinaryDeepRowsCutsAfterSpacing m K d hd v₀ β α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  exact hdeep d hd β hβ hβ1 hβα hβε hgap
end Oberwolfach
