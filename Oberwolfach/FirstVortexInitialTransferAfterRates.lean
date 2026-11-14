module

public import Oberwolfach.FirstVortexInitialGlobalTransfer

@[expose] public section
/-! The ordered caller is available after the shared early rates, while its
local and transfer caps remain available for their later choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def FirstVortexInitialTransferAfterRates
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε:ℝ):Prop :=
    ∀(localCap transferCap θUpper assignUpper:ℝ),
      0<localCap→0<transferCap→0<θUpper→0<assignUpper→
    ∃δold δlocal:ℝ,0<δold ∧ δold≤1 ∧ δold<δlocal ∧ δlocal≤δglobal ∧
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
      α ε c chosenLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap

theorem first_vortex_initial_transfer_after_rates
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ)
    (βList εLevel εAbs εRob γRich kstar tstar hostCap bmatch α ε:ℝ)
    (hcap:0<cap)
    (hGlobal:FirstVortexGlobalRatesContinuation r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε):
    FirstVortexInitialTransferAfterRates r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate α ε :=by
  intro localCap transferCap θUpper assignUpper hlocal htransfer hθUpper hAssign
  have hδglobal:0<δglobal:=hGlobal.1.2.2.2.2.2.2.1
  exact first_vortex_initial_global_transfer r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    βList εLevel εAbs εRob γRich kstar tstar hostCap bmatch α ε hcap hδglobal hGlobal hInitial
    localCap transferCap θUpper assignUpper hlocal htransfer hθUpper hAssign
end Oberwolfach
