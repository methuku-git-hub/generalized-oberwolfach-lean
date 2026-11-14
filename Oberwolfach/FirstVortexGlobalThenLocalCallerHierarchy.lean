module

public import Oberwolfach.FirstVortexPackingParametersSupplyCallerBudgets
public import Oberwolfach.FirstVortexGlobalThenLocalParameterHierarchy

@[expose] public section
/-! Package the ordered choices together with the concrete caller budgets
for each later selector output. -/
set_option autoImplicit false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexPackingWithCallerBudgets
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap:ℝ):Prop :=
    ∃t s lamAssign θ lam ξCap κPack:ℝ,
      0<t ∧ t≤localCap ∧ 0<s ∧ 0<lamAssign ∧ lamAssign≤assignUpper ∧
      0<θ ∧ θ≤s ∧ θ≤θUpper ∧
      0<κPack ∧ κPack≤s/2 ∧ κPack≤κPackCap/2 ∧ 10*θ≤κPack*(βfinal/4) ∧
      8*(θ*ε^2+lamAssign*ε)/((ρ₀/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤s ∧ lam≤lamCap ∧ ξCap≤s ∧ ξCap≤lamCap ∧
      lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
    ∃ζret ζlocal ηBalance κaux:ℝ,
      FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux ∧
    ∃KMin N:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
      5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ ∧
      ∀eps Δ ξPart:ℝ,0<eps→0≤Δ→Δ≤eps/8→0≤ξPart→ξPart≤ξCap→
        3*eps≤lam*(θ/(100*(K:ℝ)^2))→
      ∃ hδ:0<δglobal, ∃ hθ:0<θ, ∃ hθδ:10*θ≤δglobal, ∃ hspacing:1/(d:ℝ)≤θ/1024,
        FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
          ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing

theorem first_vortex_global_then_local_caller_hierarchy
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap) (hβ:0<βfinal):
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
      α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap :=by
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,
    hrho,heta,hζ,hΔ,hLoss,hInner,hδ,hθ,ht,hetaR,hInnerδ,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows,hAmbient⟩:=
    first_vortex_ambient_global_hierarchy r ρ₀ cap (βfinal/2) hρ₀ hcap (by positivity)
  have hbound:δglobal≤(βfinal/200)^2:=by convert hδbound using 1 <;> congr 1 <;> ring
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,globalRate,?_,hbound,?_⟩
  · exact ⟨hrho,heta,hζ,hΔ,hLoss,hInner,hδ,hθ,ht,hetaR,hInnerδ,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows,hAmbient⟩
  · intro α ε cLocal θUpper assignUpper δold δlocal hα hε hε1 hεinner hcLocal hθUpper hAssignUpper hδold hgap cGlobal c active θcap κCap lamCap
    have hcGlobal:0<cGlobal:=by dsimp [cGlobal];positivity
    have hc:0<c:=by dsimp [c];positivity
    have hcLocal':c≤cLocal:=min_le_left _ _
    have hcGlobal':c≤cGlobal:=min_le_right _ _
    have hactive:0<active:=by dsimp [active];positivity
    have hactiveLocal:active≤cLocal:=by dsimp [active];linarith
    have hactiveGlobal:active≤cGlobal/2:=by dsimp [active];linarith
    have hθcap:0<θcap:=by dsimp [θcap];positivity
    have hθup:θcap≤θUpper:=min_le_left _ _
    have hθmax:θcap≤θmax:=(min_le_right _ _).trans (min_le_left _ _)
    have hθold:θcap≤δold/32:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hθδ:θcap≤δglobal/10:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hθ100:θcap≤1/100:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hsqrt:0<Real.sqrt δglobal:=Real.sqrt_pos.2 hδ
    have hκ:0<κCap:=by dsimp [κCap];positivity
    have hκroot:κCap/2≤Real.sqrt δglobal/4:=by have hh:=min_le_left (Real.sqrt δglobal/2) (cGlobal/512);dsimp only [κCap];linarith
    have hκglobal:κCap/2≤cGlobal/1024:=by have hh:=min_le_right (Real.sqrt δglobal/2) (cGlobal/512);dsimp only [κCap];linarith
    have hlam:0<lamCap:=by dsimp [lamCap];positivity
    have hlamt:lamCap≤globalRate:=min_le_left _ _
    have hlamz:lamCap≤3*min ζmax Δmax:=min_le_right _ _
    refine ⟨hc,hcLocal',hcGlobal',hactive,hactiveLocal,hactiveGlobal,hθcap,hθup,hθmax,by linarith,hθold,by linarith,hθ100,hκ,hκroot,hκglobal,hlam,hlamt,hlamz,?_⟩
    have hData:FirstVortexAmbientGlobalData r ρ₀ cap (βfinal/2) rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate:=
      ⟨hrho,heta,hζ,hΔ,hLoss,hInner,hδ,hθ,ht,hetaR,hInnerδ,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows,hAmbient⟩
    have hPack:FirstVortexOrderedPackingData r α ε c rho eta (min eta globalRate) active θcap assignUpper δold δlocal ρ₀ lamCap βfinal κCap:=
      first_vortex_ordered_summed_loss_packing_parameters r α ε c rho eta (min eta globalRate) active θcap assignUpper δold δlocal ρ₀ lamCap βfinal κCap
        hα hε hε1 hc hrho heta (by positivity) hactive hθcap hAssignUpper hδold hgap hρ₀ hlam hβ hκ
    exact first_vortex_packing_parameters_supply_caller_budgets r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax globalRate
      α ε c cLocal (min eta globalRate) active θcap assignUpper δold δlocal lamCap κCap
      hρ₀ hβ hε hεinner hactive hcLocal' hcGlobal' hθmax (by linarith) (by linarith) hκroot hκglobal (le_min hlamt hlamz) hData hPack
end Oberwolfach
