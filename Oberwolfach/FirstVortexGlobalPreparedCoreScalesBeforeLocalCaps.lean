module

public import Oberwolfach.FirstVortexGlobalPreparedScalesBeforeLocalCaps

@[expose] public section
/-! Choose the actual vortex scale below all positive caps used in the
    structural-core probability theorem, together with the same solver. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_prepared_core_scales_before_local_caps
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hρone:ρ₀≤1) (hcap:0<cap) (hβ:0<βfinal) (hm:7≤r+4):
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∀(αUpper εAbs εRob γRich kstar tstar εListCap:ℝ),
      0<αUpper→0<εAbs→0<εRob→0<γRich→0<kstar→0<tstar→0<εListCap→
    ∃α ε δold δlocal bmatch:ℝ,
      0<α ∧ α≤αUpper ∧ 0<ε ∧ ε<1/4 ∧ ε≤εInner ∧ ε≤εAbs ∧ ε≤εRob ∧
      ε≤min ((γRich/2)*kstar) tstar/128 ∧ ε≤εListCap ∧ ε≤α/100000 ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧ δlocal≤δglobal ∧
      0<bmatch ∧ (2*α)/16≤bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧ ε≤α/1000 ∧
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
      α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap bmatch :=by
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδstrong,hLocal⟩:=
    first_vortex_global_prepared_scales_before_local_caps r ρ₀ cap βfinal hρ₀ hρone hcap hβ hm
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδstrong,?_⟩
  intro αUpper εAbs εRob γRich kstar tstar εListCap hαUpper hAbs hRob hγ hk ht hList
  let εUpper:ℝ:=min εAbs (min εRob (min (((γRich/2)*kstar)/128) (min (tstar/128) εListCap)))
  have hUpper:0<εUpper:=by dsimp [εUpper];positivity
  obtain ⟨α,ε,δold,δlocal,bmatch,hα,hαcap,hε,hεquarter,hεinner,hεcap,hδold,hδold1,hδoldGlobal,hgap,hδlocalEq,hlocalGlobal,hb,hαb,hbcap,hερ,hεprecise,hεαstrong,hεα,hResult⟩:=
    hLocal αUpper εUpper hαUpper hUpper
  have hAbsCap:ε≤εAbs:=hεcap.trans (min_le_left _ _)
  have hRobCap:ε≤εRob:=hεcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRichCap:ε≤((γRich/2)*kstar)/128:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hTimeCap:ε≤tstar/128:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hListCap:ε≤εListCap:=hεcap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hSmall:ε≤min ((γRich/2)*kstar) tstar/128:=by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<128)).2
    apply le_min <;> linarith
  exact ⟨α,ε,δold,δlocal,bmatch,hα,hαcap,hε,hεquarter,hεinner,hAbsCap,hRobCap,hSmall,hListCap,hεαstrong,hδold,hδold1,hδoldGlobal,hgap,hδlocalEq,hlocalGlobal,hb,hαb,hbcap,hερ,hεprecise,hεα,hResult⟩
end Oberwolfach
