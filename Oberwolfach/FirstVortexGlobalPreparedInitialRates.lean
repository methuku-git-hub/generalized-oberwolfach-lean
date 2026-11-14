module

public import Oberwolfach.FirstVortexGlobalPreparedCoreScales
public import Oberwolfach.FirstVortexInitialMatchingVortexRates

@[expose] public section
/-! Derive the complete initial matching-vortex rate bundle from earlier
    positive caps and the strictly positive list margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_prepared_initial_rates
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hρone:ρ₀≤1) (hcap:0<cap) (hβ:0<βfinal) (hm:7≤r+4):
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
      FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate ∧
      δglobal≤(βfinal/200)^2 ∧
    ∀(αHostUpper βList εLevel εAbs εRob γRich kstar tstar hostCap εExtra cLocal θUpper assignUpper:ℝ),
      0<αHostUpper→βfinal<βList→0<εLevel→0<εAbs→0<εRob→0<γRich→0<kstar→0<tstar→0<hostCap→0<εExtra→0<cLocal→0<θUpper→0<assignUpper→
    ∃α ε δold δlocal bmatch:ℝ,
      α≤αHostUpper ∧ ε≤εExtra ∧
      FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε ∧
      0<δold ∧ δold≤1 ∧ δold≤δglobal ∧ δold<δlocal ∧ δlocal=2*δold ∧
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
    first_vortex_global_prepared_core_scales r ρ₀ cap βfinal hρ₀ hρone hcap hβ hm
  have hδ:0<δglobal:=by
    rcases hAmbient with ⟨_,_,_,_,_,_,h,_⟩
    exact h
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,hAmbient,hδstrong,?_⟩
  intro αHostUpper βList εLevel εAbs εRob γRich kstar tstar hostCap εExtra cLocal θUpper assignUpper
    hαUpper hList hLevel hAbs hRob hγ hk ht hHost hExtra hc hθ hAssign
  let αUpper:ℝ:=min αHostUpper (2*δglobal)
  let εListCap:ℝ:=min εLevel (min hostCap (min δglobal (min (βList-βfinal) εExtra)))
  have hαcapPos:0<αUpper:=by dsimp [αUpper];positivity
  have hεcapPos:0<εListCap:=by dsimp [εListCap];positivity
  obtain ⟨α,ε,δold,δlocal,bmatch,hα,hαcap,hε,hεquarter,hεinner,hεAbs,hεRob,hεsmall,hεList,hεαstrong,hδold,hδold1,hδoldGlobal,hgap,hδlocalEq,hb,hαb,hbcap,hερ,hεprecise,hεα,hResult⟩:=
    hLocal αUpper εAbs εRob γRich kstar tstar εListCap cLocal θUpper assignUpper hαcapPos hAbs hRob hγ hk ht hεcapPos hc hθ hAssign
  have hαHost:α≤αHostUpper:=hαcap.trans (min_le_left _ _)
  have hαGlobal:2*α≤4*δglobal:=by
    have h:=hαcap.trans (min_le_right αHostUpper (2*δglobal))
    linarith
  have hεLevel:ε≤εLevel:=hεList.trans (min_le_left _ _)
  have hεHost:ε≤hostCap:=hεList.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεGlobal:ε≤δglobal:=hεList.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεDiff:ε≤βList-βfinal:=hεList.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεExtra:ε≤εExtra:=hεList.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hεHostMargin:ε≤(2*α)/100000:=by linarith
  have hRates:FirstVortexInitialMatchingVortexRates ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε:=by
    exact ⟨hb,hbcap,hα,hαb,hαGlobal,hε,hεquarter,hεLevel,hεinner,hεAbs,hεRob,hεHost,hεsmall,hεHostMargin,hεα,hερ,hεprecise,hεGlobal,by linarith⟩
  exact ⟨α,ε,δold,δlocal,bmatch,hαHost,hεExtra,hRates,hδold,hδold1,hδoldGlobal,hgap,hδlocalEq,hResult⟩
end Oberwolfach
