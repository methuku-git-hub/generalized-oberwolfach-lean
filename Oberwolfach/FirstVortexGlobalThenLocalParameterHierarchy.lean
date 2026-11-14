module

public import Oberwolfach.FirstVortexAmbientGlobalHierarchy
public import Oberwolfach.FirstVortexOrderedSummedLossPackingParameters

@[expose] public section
/-! Fix the global loss and supply before the vortex scale; after the local
balance cap arrives, choose matching, packing and retention on compatible rates. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexAmbientGlobalData
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ):Prop :=
  let c:=min cap (1:ℝ);
      0<rho ∧ 0<eta ∧ 0<ζmax ∧ 0<Δmax ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ 0<θmax ∧ 0<t ∧ eta≤rho ∧ εInner≤δglobal/8 ∧
      5*Real.sqrt δglobal≤δLoss ∧ δglobal≤(βfinal/100)^2 ∧
      10*θmax≤δglobal ∧ θmax≤c/1024 ∧ δglobal+Real.sqrt δglobal≤c/1024 ∧ ζmax≤cap ∧
      (∀ζ:ℝ,0≤ζ→ζ≤ζmax→ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))) ∧
      (∀θ Δ a γ ξClass:ℝ,θ≤θmax→Δ≤Δmax→a≤t→γ≤t→ξClass≤t→
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<c/2048) ∧
      (∀θ ζret refRate:ℝ,θ≤θmax→ζret≤c/1024→ refRate≤c/1024→
        2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(c/1024)<c/2 ∧
        2*(ζret+10*θ)+refRate≤c/2) ∧
      ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀κ:ℝ,0≤κ→κ≤Real.sqrt δglobal/4→
        δglobal+κ≤Real.sqrt δglobal ∧
        2*(δglobal*(n:ℝ)+(κ*(n:ℝ)+1))≤δLoss*(n:ℝ) ∧
        εInner*(n:ℝ)+((6*d+2:ℕ):ℝ)≤δglobal*(n:ℝ)/4

def FirstVortexOrderedPackingData
    (r:ℕ) (α ε c rho eta localCap active θUpper assignUpper δold δlocal ρmatch globalRate βfinal κPackCap:ℝ):Prop :=
    ∃t s lamAssign θ lam ξCap κPack:ℝ,
      0<t ∧ t≤localCap ∧ 0<s ∧ 0<lamAssign ∧ lamAssign≤assignUpper ∧
      0<θ ∧ θ≤s ∧ θ≤θUpper ∧
      0<κPack ∧ κPack≤s/2 ∧ κPack≤κPackCap/2 ∧ 10*θ≤κPack*(βfinal/4) ∧
      8*(θ*ε^2+lamAssign*ε)/((ρmatch/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤s ∧ lam≤globalRate ∧ ξCap≤s ∧ ξCap≤globalRate ∧
      lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
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
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ

theorem first_vortex_global_then_local_parameter_hierarchy
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
    FirstVortexOrderedPackingData r α ε c rho eta (min eta globalRate) active θcap assignUpper δold δlocal ρ₀ lamCap βfinal κCap :=by
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
    exact first_vortex_ordered_summed_loss_packing_parameters r α ε c rho eta (min eta globalRate) active θcap assignUpper δold δlocal ρ₀ lamCap βfinal κCap
      hα hε hε1 hc hrho heta (by positivity) hactive hθcap hAssignUpper hδold hgap hρ₀ hlam hβ hκ
end Oberwolfach
