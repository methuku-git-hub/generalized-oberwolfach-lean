module

public import Oberwolfach.FirstVortexOriginalPreparedLateCapAndLocalContract

@[expose] public section
/-! After fixing the vortex, retain the preparation solver uniformly for
all later level-dependent local caps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexCallerLocalLateCaps
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ)
    (α ε δold δlocal bmatch:ℝ):Prop :=
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
end Oberwolfach
