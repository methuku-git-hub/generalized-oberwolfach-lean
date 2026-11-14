module

public import Oberwolfach.FirstVortexParentExactGlobalCallerHierarchy

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexGlobalRatesContinuation
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ):Prop :=
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∀(α ε cLocal θUpper assignUpper δold δlocal:ℝ),
      0<α→0<ε→ε≤1/4→ε≤εInner→0<cLocal→0<θUpper→0<assignUpper→0<δold→δold<δlocal→
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
    FirstVortexPackingWithCallerBudgets r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap
end Oberwolfach
