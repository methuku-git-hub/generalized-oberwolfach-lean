module

public import Oberwolfach.FirstVortexCallerLocalLateCaps

@[expose] public section
/-! Choose the local matching rate below both the level balance cap and the
active-transfer cap, while keeping the prepared solver on those choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_prepared_local_for_transfer
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ)
    (α ε δold δlocal bmatch localCap transferCap:ℝ)
    (hLocal:0<localCap) (hTransfer:0<transferCap)
    (h:FirstVortexCallerLocalLateCaps r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε δold δlocal bmatch):
    let cGlobal:=min cap (1:ℝ)
    let chosenLocal:=min localCap (4*transferCap)
    let c:=min chosenLocal cGlobal
    let active:=c/4
    let θcap:=min (1:ℝ) (min θmax (min (δold/32) (min (δglobal/10) (1/100:ℝ))))
    let κCap:=min (Real.sqrt δglobal/2) (cGlobal/512)
    let lamCap:=min globalRate (3*min ζmax Δmax);
    0<chosenLocal ∧ chosenLocal≤localCap ∧ 0<c ∧ 0<active ∧
      active≤localCap ∧ active≤transferCap ∧ active≤cGlobal/2 ∧
      0<θcap ∧ θcap≤1 ∧ θcap≤θmax ∧ 10*θcap≤δold ∧ θcap≤δold/32 ∧
      10*θcap≤δglobal ∧ θcap≤1/100 ∧ 0<κCap ∧ 0<lamCap ∧
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c chosenLocal (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch:=by
  intro cGlobal chosenLocal c active θcap κCap lamCap
  have hchosen:0<chosenLocal:=by dsimp [chosenLocal];positivity
  have hchosenLocal:chosenLocal≤localCap:=min_le_left _ _
  have hchosenTransfer:chosenLocal≤4*transferCap:=min_le_right _ _
  have hh:=h chosenLocal 1 1 hchosen (by norm_num) (by norm_num)
  obtain ⟨hc,hcLocal,hcGlobal,hactive,hactiveLocal,hactiveGlobal,hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hκroot,hκglobal,hlam,hlamglobal,hlamRates,hprepared⟩:=hh
  have hactiveCap:active≤localCap:=hactiveLocal.trans hchosenLocal
  have hactiveTransfer:active≤transferCap:=by dsimp [active];linarith
  exact ⟨hchosen,hchosenLocal,hc,hactive,hactiveCap,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,hprepared⟩
end Oberwolfach
