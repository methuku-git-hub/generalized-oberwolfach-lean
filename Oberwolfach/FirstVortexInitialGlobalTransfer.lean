module

public import Oberwolfach.FirstVortexGlobalTransferCaller
public import Oberwolfach.FirstVortexInitialMatchingVortexRates

@[expose] public section
/-! Feed the initial vortex and matching rates into the ordered global/local
caller, choosing the two deletion rates before the later selector choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_initial_global_transfer
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ)
    (βList εLevel εAbs εRob γRich kstar tstar hostCap bmatch α ε:ℝ)
    (hcap:0<cap) (hδglobal:0<δglobal)
    (hGlobal:FirstVortexGlobalRatesContinuation r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate)
    (hInitial:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε)
    (localCap transferCap θUpper assignUpper:ℝ)
    (hlocal:0<localCap) (htransfer:0<transferCap) (hθUpper:0<θUpper) (hAssign:0<assignUpper):
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
      α ε c chosenLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap :=by
  rcases hInitial with ⟨_,_,hα,_,_,hε,hεquarter,_,hεinner,_⟩
  let δold:=min δglobal (1:ℝ)/4
  let δlocal:=min δglobal (1:ℝ)/2
  have hmin:0<min δglobal (1:ℝ):=lt_min hδglobal (by norm_num)
  have hmin1:min δglobal (1:ℝ)≤1:=min_le_right _ _
  have hming:min δglobal (1:ℝ)≤δglobal:=min_le_left _ _
  have hold:0<δold:=by dsimp [δold];positivity
  have hold1:δold≤1:=by dsimp [δold];linarith
  have hgap:δold<δlocal:=by dsimp [δold,δlocal];linarith
  have hlocalglobal:δlocal≤δglobal:=by dsimp [δlocal];linarith
  refine ⟨δold,δlocal,hold,hold1,hgap,hlocalglobal,?_⟩
  exact first_vortex_global_transfer_caller r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    hcap hGlobal α ε localCap transferCap θUpper assignUpper δold δlocal
    hα hε hεquarter.le hεinner hlocal htransfer hθUpper hAssign hold hgap
end Oberwolfach
