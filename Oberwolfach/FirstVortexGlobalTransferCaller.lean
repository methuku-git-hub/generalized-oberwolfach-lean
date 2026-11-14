module

public import Oberwolfach.FirstVortexGlobalRatesContinuation
public import Oberwolfach.FirstVortexSummedLossMonotone

@[expose] public section
/-! Choose the local caller budget after the active-transfer threshold is
known, while preserving the earlier global rates and the caller tolerance. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_transfer_caller
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ)
    (hcap:0<cap)
    (hGlobal:FirstVortexGlobalRatesContinuation r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate)
    (α ε localCap transferCap θUpper assignUpper δold δlocal:ℝ)
    (hα:0<α) (hε:0<ε) (hε1:ε≤1/4) (hεinner:ε≤εInner)
    (hlocal:0<localCap) (htransfer:0<transferCap) (hθUpper:0<θUpper)
    (hAssign:0<assignUpper) (hδ:0<δold) (hgap:δold<δlocal):
    let cGlobal:=min cap (1:ℝ)
    let chosenLocal:=min localCap (4*transferCap)
    let c:=min chosenLocal cGlobal
    let active:=c/4
    let θcap:=min θUpper (min θmax (min (δold/32) (min (δglobal/10) (1/100:ℝ))))
    let κCap:=min (Real.sqrt δglobal/2) (cGlobal/512)
    let lamCap:=min globalRate (3*min ζmax Δmax);
    0<chosenLocal ∧ chosenLocal≤localCap ∧ 0<c ∧ 0<active ∧
      active≤localCap ∧ active≤transferCap ∧ active≤cGlobal/2 ∧
      0<θcap ∧ θcap≤θUpper ∧ θcap≤θmax ∧ 10*θcap≤δold ∧ θcap≤δold/32 ∧
      10*θcap≤δglobal ∧ θcap≤1/100 ∧ 0<κCap ∧ 0<lamCap ∧
    FirstVortexPackingWithCallerBudgets r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c chosenLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap :=by
  intro cGlobal chosenLocal c active θcap κCap lamCap
  have hcGlobal:0<cGlobal:=by dsimp [cGlobal]; positivity
  obtain ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal⟩:=
    first_vortex_joint_local_transfer_caps localCap transferCap cGlobal hlocal htransfer hcGlobal
  obtain ⟨_,_,hLater⟩:=hGlobal
  have hh:=hLater α ε chosenLocal θUpper assignUpper δold δlocal hα hε hε1 hεinner hchosen hθUpper hAssign hδ hgap
  obtain ⟨_,_,_,_,_,_,hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,_,_,hlam,_,_,hPack⟩:=hh
  exact ⟨hchosen,hchosenLocal,hc,hactive,hactiveLocal,hactiveTransfer,hactiveGlobal,hθ,hθup,hθmax,hθold,hθold32,hθglobal,hθ100,hκ,hlam,hPack⟩
end Oberwolfach
