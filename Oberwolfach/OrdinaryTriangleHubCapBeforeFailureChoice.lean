module

public import Oberwolfach.OrdinaryTriangleHubEarlyBeforeFailure
public import Oberwolfach.OrdinaryTriangleHubAfterCapBeforeFailure

@[expose] public section
/-! Fix triangle trace and edit caps before all failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_hub_cap_before_failure_choice
    (α ρ₀ pmin κ c C:ℝ) (htri:OrdinaryTriangleHubEarlyBeforeFailure α ρ₀ pmin κ c C)
    (aLoad ε:ℝ) (haLoad:0<aLoad) (haκ:aLoad≤κ) (hε:0<ε) (hε1:ε<1/4) (hεκ:ε≤κ) (hερ:ε≤ρ₀/16)
    (d:ℕ) (hd:2≤d) (ξ b Bweight ηHub Kdom ηbal ζlimit:ℝ)
    (hξ:0<ξ) (hηbal:0<ηbal) (hζlimit:0<ζlimit)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom) (hb:b≤c)
    (hB:(4*C/pmin^(3*2+1))*Kdom^2≤Bweight) (buffer:ℕ) (hbuffer:2≤buffer):
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d buffer ∧
      OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap :=by
  exact htri aLoad haLoad haκ ε hε hε1 hεκ hερ d hd ξ b Bweight ηHub Kdom ηbal ζlimit
    hξ hηbal hζlimit hKdom hb hB buffer hbuffer
end Oberwolfach
