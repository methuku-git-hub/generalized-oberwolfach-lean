module

public import Oberwolfach.FirstVortexPreparedLocalForTransfer
public import Oberwolfach.FirstVortexPreparedLocalCapMono

@[expose] public section
/-! Choose the local matching rate below both the level balance cap and the
active-transfer cap, while keeping the prepared solver on those choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_prepared_local_for_transfer_exact_budget
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
      α ε c localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch:=by
  intro cGlobal chosenLocal c active θcap κCap lamCap
  have hh:=first_vortex_prepared_local_for_transfer r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε δold δlocal bmatch localCap transferCap hLocal hTransfer h
  obtain ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,hprepared⟩:=hh
  refine ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,
    hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,?_⟩
  exact first_vortex_prepared_local_cap_mono r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε c chosenLocal localCap (min eta globalRate) active θcap 1 δold δlocal lamCap κCap bmatch hchosenLocal hprepared
end Oberwolfach
