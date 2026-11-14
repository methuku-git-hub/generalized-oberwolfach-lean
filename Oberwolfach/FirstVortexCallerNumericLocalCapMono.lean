module

public import Oberwolfach.FirstVortexActualCallerNumericResult
public import Oberwolfach.FirstVortexSummedLossLocalCapMono

@[expose] public section
/-! The original caller numerics can be reused at a larger local budget;
all matching, loss and host parameters stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_caller_numeric_local_cap_mono
    (r d K:ℕ) (ρ₀ cap rho eta δLoss εInner δglobal:ℝ)
    (ε cLocal cLocal' active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal:ℝ)
    (hδ:0<δglobal) (hθ:0<θ) (hθδ:10*θ≤δglobal) (hspacing:1/(d:ℝ)≤θ/1024)
    (hc:cLocal≤cLocal')
    (h:FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
      ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing):
    FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
      ε cLocal' active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing:=by
  obtain ⟨h1,h2,h3,N,hN⟩:=h
  refine ⟨h1,h2,h3,N,?_⟩
  intro n hn U _ G D m β Q hm hu I boundary
  obtain ⟨hn0,h100,h200,hsqrt,hNlocal,hθκ,hδκ,hloss,hinner,hI,hmax,hactive,hceiling,hrow,hcol,hwitness⟩:=
    hN n hn U G D m β Q hm hu
  refine ⟨hn0,h100,h200,hsqrt,hNlocal,hθκ,hδκ,hloss,hinner,hI,hmax,hactive,hceiling,hrow,hcol,?_⟩
  exact first_vortex_summed_loss_local_cap_mono n d I cLocal cLocal' rho eta θ _ _ ξPart κPack Δ ζret ηBalance boundary
    (by dsimp [I];positivity) hc hwitness
end Oberwolfach
