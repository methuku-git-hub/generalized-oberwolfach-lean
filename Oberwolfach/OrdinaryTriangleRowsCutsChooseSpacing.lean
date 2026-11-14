module

public import Oberwolfach.OrdinaryTriangleRowsCutsAfterSpacing

@[expose] public section
/-! Choose the terminal size threshold after the triangle error rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_rows_cuts_choose_spacing
    (α ρ₀ pmin κ:ℝ) (htri:OrdinaryTriangleRowsCutsAfterEarly α ρ₀ pmin κ)
    (aLoad ε χdeep β:ℝ) (haLoad:0<aLoad) (haκ:aLoad≤κ) (hε:0<ε) (hε1:ε<1/4)
    (hεκ:ε≤κ) (hερ:ε≤ρ₀/16) (hχdeep:0<χdeep) (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hβκ:β≤κ)
    (d:ℕ) (hd:2≤d) (εR εH χone χtwo χcut:ℝ) (hεR:0<εR) (hεH:0<εH) (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut):
    ∃v₀:ℕ,1≤v₀ ∧ OrdinaryTriangleRowsCutsAfterSpacing d v₀ hd α ρ₀ pmin κ aLoad ε χdeep β εR εH χone χtwo χcut :=by
  exact htri aLoad haLoad haκ ε χdeep hε hε1 hεκ hερ hχdeep β hβ hβ1 hβα hβκ d hd εR εH χone χtwo χcut hεR hεH hχone hχtwo hχcut
end Oberwolfach
