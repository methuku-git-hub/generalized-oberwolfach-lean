module

public import Oberwolfach.FirstVortexSplitGlobalChangeEventually

@[expose] public section
/-! Convert the early global rate margins into the exact ambient row and
column bounds required by the same-sample caller. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_ambient_global_eventual_budgets
    (d:ℕ) (c ζret δ ηBalance θ a γ ξPart κ Δ rho eta:ℝ)
    (hc:0<c) (hδ:0≤δ) (hδsum:δ+Real.sqrt δ≤c/1024)
    (hζ:ζret≤c/1024) (hbal:ηBalance≤c/1024) (hκ:κ≤c/1024)
    (hbase:2*θ+2*max a (4*γ)+2*ξPart+5*Real.sqrt δ+2*Δ+(1+2/rho)*eta<c/2048)
    (hcol:2*(ζret+10*θ)+ηBalance≤c/2):
    ∃N:ℕ,∀n:ℕ,N≤n→
      2*(ζret*n+(δ*n+(Real.sqrt δ*n+1)))+
        (ηBalance*n+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δ*n+(κ*n+1)))+
          (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)))≤(c/2)*n ∧
      2*(ζret*n+10*θ*n)+ηBalance*n≤(c/2)*n :=by
  have hsqrt:0≤Real.sqrt δ:=Real.sqrt_nonneg _
  have hrow:2*(ζret+δ+Real.sqrt δ)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δ+κ)+2*Δ+(1+2/rho)*eta)<c/2:=by
    nlinarith only [hc,hδ,hsqrt,hδsum,hζ,hbal,hκ,hbase]
  exact first_vortex_split_global_change_eventually d ζret δ ηBalance θ a γ ξPart δ κ Δ rho eta (c/2) hrow hcol
end Oberwolfach
