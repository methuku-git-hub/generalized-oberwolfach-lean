module

public import Oberwolfach.FirstVortexGlobalThenLocalPreparedHierarchy
public import Oberwolfach.FirstVortexPreparedLocalChoicesStrong

@[expose] public section
/-! Choose all the local auxiliary scales after the global data and under
    arbitrary positive local caps, retaining the matched preparation solver. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_then_local_prepared_scales_strong
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hρone:ρ₀≤1) (hcap:0<cap) (hβ:0<βfinal) (hm:7≤r+4):
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∀(αUpper εUpper cLocal θUpper assignUpper:ℝ),
      0<αUpper→0<εUpper→0<cLocal→0<θUpper→0<assignUpper→
    ∃α ε δold δlocal bmatch:ℝ,
      0<α ∧ α≤αUpper ∧ 0<ε ∧ ε<1/4 ∧ ε≤εInner ∧ ε≤εUpper ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧
      0<bmatch ∧ (2*α)/16≤bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧ ε≤α/100000 ∧ ε≤α/1000 ∧
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
    first_vortex_global_then_local_prepared_hierarchy r ρ₀ cap βfinal hρ₀ hρone hcap hβ hm
  have hInner:0<εInner:=by
    rcases hAmbient with ⟨_,_,_,_,_,h,_⟩
    exact h
  have hδ:0<δglobal:=by
    rcases hAmbient with ⟨_,_,_,_,_,_,h,_⟩
    exact h
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδstrong,?_⟩
  intro αUpper εUpper cLocal θUpper assignUpper hαUpper hεUpper hc hθ hAssign
  obtain ⟨α,ε,δold,δlocal,bmatch,hα,hαcap,hε,hεquarter,hεinner,hεcap,hδold,hδold1,hδoldGlobal,hgap,hδlocalEq,hb,hαb,hbcap,hερ,hεprecise,hεαstrong,hεα⟩:=
    first_vortex_prepared_local_choices_strong ρ₀ δglobal εInner αUpper εUpper hρ₀ hδ hInner hαUpper hεUpper
  refine ⟨α,ε,δold,δlocal,bmatch,hα,hαcap,hε,hεquarter,hεinner,hεcap,hδold,hδold1,hδoldGlobal,hgap,hδlocalEq,hb,hαb,hbcap,hερ,hεprecise,hεαstrong,hεα,?_⟩
  exact hLocal α ε cLocal θUpper assignUpper δold δlocal bmatch hα hε (le_of_lt hεquarter) hεinner hc hθ hAssign hδold hδold1 hgap hb hαb hbcap hερ hεprecise hεα
end Oberwolfach
