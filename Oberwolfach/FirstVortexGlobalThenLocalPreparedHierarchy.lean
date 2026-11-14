module

public import Oberwolfach.FirstVortexGlobalThenLocalCallerHierarchy
public import Oberwolfach.FirstVortexCallerParametersPrepared

@[expose] public section
/-! The global-to-local caller hierarchy directly supplies the concrete
    boundary solver at the very same matching and retention parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_then_local_prepared_hierarchy
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hρone:ρ₀≤1) (hcap:0<cap) (hβ:0<βfinal) (hm:7≤r+4):
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∀(α ε cLocal θUpper assignUpper δold δlocal bmatch:ℝ),
      0<α→0<ε→ε≤1/4→ε≤εInner→0<cLocal→0<θUpper→0<assignUpper→0<δold→δold≤1→δold<δlocal→
      0<bmatch→(2*α)/16≤bmatch→bmatch≤((ρ₀/4)/40000)/16→
      ε≤(ρ₀/4)/80000→ε≤((ρ₀/4)/40000)/8192→ε≤α/1000→
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
      α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap bmatch :=by
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδstrong,hLocal⟩:=
    first_vortex_global_then_local_caller_hierarchy r ρ₀ cap βfinal hρ₀ hcap hβ
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδstrong,?_⟩
  intro α ε cLocal θUpper assignUpper δold δlocal bmatch hα hε hε1 hεinner hcLocal hθUpper hAssignUpper hδold hδold1 hgap hbmatch hαb hbd hεsmall hprecise hεalpha cGlobal c active θcap κCap lamCap
  obtain ⟨hc,hcLocal,hcGlobal,hactive,hactiveLocal,hactiveGlobal,hθcap,hθup,hθmax,hθδold,hθold,hθδglobal,hθ100,hκ,hκroot,hκglobal,hlam,hlamt,hlamz,hPack⟩:=
    hLocal α ε cLocal θUpper assignUpper δold δlocal hα hε hε1 hεinner hcLocal hθUpper hAssignUpper hδold hgap
  refine ⟨hc,hcLocal,hcGlobal,hactive,hactiveLocal,hactiveGlobal,hθcap,hθup,hθmax,hθδold,hθold,hθδglobal,hθ100,hκ,hκroot,hκglobal,hlam,hlamt,hlamz,?_⟩
  have hChosen:=first_vortex_caller_parameters_chosen r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap hPack
  exact first_vortex_caller_prepared_solver_same_choices r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
    α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap bmatch
    hα hε hδold hδold1 hρ₀ hρone hbmatch hαb hbd hεsmall hprecise hεalpha hθold hθ100 hm hChosen
end Oberwolfach
