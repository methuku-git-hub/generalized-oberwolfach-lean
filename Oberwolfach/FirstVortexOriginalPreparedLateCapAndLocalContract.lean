module

public import Oberwolfach.FirstVortexOriginalPreparedRatesLateCapAndLocal

@[expose] public section
/-! The list and reserve budgets precede the global cap, and the vortex
scale precedes the level-dependent local caps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexOriginalPreparedLateCapAndLocalContract (r:ℕ) (ρ₀ αRef:ℝ):Prop :=
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃βfinal ρreserve:ℝ, 0<βfinal ∧ βfinal≤1 ∧ βfinal≤βList/4 ∧ 0<ρreserve ∧ βfinal+2*ρreserve≤βList/2 ∧
      (∀e₀:ℕ, ∃N:ℕ, ∀n:ℕ,N≤n→(e₀:ℝ)≤ρreserve*n) ∧
    ∀cap:ℝ,0<cap→∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∀(αHostUpper εLevel εAbs εRob γRich kstar tstar hostCap εExtra:ℝ),
      0<αHostUpper→0<εLevel→0<εAbs→0<εRob→0<γRich→0<kstar→0<tstar→0<hostCap→0<εExtra→
    ∃α ε δold δlocal bmatch:ℝ,
      α≤αHostUpper ∧ ε≤εExtra ∧
      FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧ δlocal≤δglobal ∧
    ∀(cLocal θUpper assignUpper:ℝ),0<cLocal→0<θUpper→0<assignUpper→
    let cGlobal:=min cap (1:ℝ);
    let c:=min cLocal cGlobal;
    let active:=c/4;
    let θcap:=min θUpper (min θmax (min (δold/32) (min (δglobal/10) (1/100:ℝ))));
    let κCap:=min (Real.sqrt δglobal/2) (cGlobal/512);
    let lamCap:=min globalRate (3*min ζmax Δmax);
    0<c ∧ c≤cLocal ∧ c≤cGlobal ∧ 0<active ∧ active≤cLocal ∧ active≤cGlobal/2 ∧
    0<θcap ∧ θcap≤θUpper ∧ θcap≤θmax ∧ 10*θcap≤δold ∧ θcap≤δold/32 ∧
      10*θcap≤δglobal ∧ θcap≤1/100 ∧
    0<κCap ∧ κCap/2≤Real.sqrt δglobal/4 ∧ κCap/2≤cGlobal/1024 ∧
    0<lamCap ∧ lamCap≤globalRate ∧ lamCap≤3*min ζmax Δmax ∧
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap bmatch 

theorem first_vortex_original_prepared_late_cap_and_local_contract
    (r:ℕ) (ρ₀ αRef:ℝ) (hρ₀:0<ρ₀) (hρone:ρ₀≤1) (hαRef:0<αRef) (hm:7≤r+4):
    FirstVortexOriginalPreparedLateCapAndLocalContract r ρ₀ αRef :=by
  exact first_vortex_original_prepared_rates_late_cap_and_local r ρ₀ αRef hρ₀ hρone hαRef hm
end Oberwolfach
