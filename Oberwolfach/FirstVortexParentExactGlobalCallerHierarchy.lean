module

public import Oberwolfach.FirstVortexGlobalThenLocalCallerHierarchy
public import Oberwolfach.MarkedVortexFixedMarginLocalCorrectionCap

@[expose] public section
/-! Fix the exact parent transfer cap and stable cap before choosing the
vortex scale, while retaining the complete ordered caller budget hierarchy. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexGlobalThenLocalCallerData (r:ℕ) (ρ₀ cap βfinal:ℝ):Prop :=
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:ℝ,
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

theorem first_vortex_parent_exact_global_caller_hierarchy
    (r:ℕ) (κ αParent ρ₀ plo klo tstar kstar ζFixed thetaDeep B pstar stableCap βfinal:ℝ)
    (hκ:0<κ) (hα:0<αParent) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1)
    (hplo:0<plo) (hklo:0<klo) (htstar:0<tstar) (hζFixed:0<ζFixed)
    (hθDeep:0<thetaDeep) (hB:0≤B) (hpstar:0<pstar) (hstable:0<stableCap) (hβ:0<βfinal):
    let exactCap:=Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ αParent (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ)
      B pstar (1:ℝ) (1:ℝ) (1:ℝ) hκ hα (by positivity) hplo hklo htstar hζFixed hθDeep (by norm_num)
      hB hpstar (by norm_num) (by norm_num) (by norm_num));
    ∃cap:ℝ,0<cap ∧ cap≤exactCap ∧ cap≤stableCap ∧ FirstVortexGlobalThenLocalCallerData r ρ₀ cap βfinal :=by
  intro exactCap
  have hExact:0<exactCap:=(Classical.choose_spec (marked_vortex_fixed_margin_local_correction_cap r κ αParent (ρ₀/4) plo klo tstar kstar ζFixed thetaDeep (1:ℝ)
      B pstar (1:ℝ) (1:ℝ) (1:ℝ) hκ hα (by positivity) hplo hklo htstar hζFixed hθDeep (by norm_num)
      hB hpstar (by norm_num) (by norm_num) (by norm_num))).1
  let cap:=min exactCap stableCap/2
  have hcap:0<cap:=by dsimp [cap];positivity
  have hcapExact:cap≤exactCap:=by dsimp [cap];have hh:=min_le_left exactCap stableCap;linarith
  have hcapStable:cap≤stableCap:=by dsimp [cap];have hh:=min_le_right exactCap stableCap;linarith
  exact ⟨cap,hcap,hcapExact,hcapStable,first_vortex_global_then_local_caller_hierarchy r ρ₀ cap βfinal hρ₀ hcap hβ⟩
end Oberwolfach
