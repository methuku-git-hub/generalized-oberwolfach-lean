module

public import Oberwolfach.FirstVortexCallerParametersPrepared
public import Oberwolfach.FirstVortexCallerNumericLocalCapMono

@[expose] public section
/-! Widen the local budget in the prepared caller without changing any
matching, retention, vortex, or sample-dependent choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_prepared_local_cap_mono
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal cLocal' localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch:ℝ)
    (hcc:cLocal≤cLocal')
    (h:FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch):
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal' localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch:=by
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθUpper,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hClassCap,hD⟩:=h
  refine ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθUpper,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hClassCap,?_⟩
  intro dExtra
  obtain ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,hK⟩:=hD dExtra
  refine ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,?_⟩
  intro KExtra
  obtain ⟨K,hKExtra,hK3,hcutHost,hNumeric,hSelectorNumeric⟩:=hK KExtra
  refine ⟨K,hKExtra,hK3,hcutHost,hNumeric,?_⟩
  intro eps Δ ξPart heps hΔ0 hΔ hξPart0 hξPart hEpsRate
  obtain ⟨hδ,hθ',hθglobal,hspacing',hNum,hSolver⟩:=hSelectorNumeric eps Δ ξPart heps hΔ0 hΔ hξPart0 hξPart hEpsRate
  refine ⟨hδ,hθ',hθglobal,hspacing',?_,hSolver⟩
  exact first_vortex_caller_numeric_local_cap_mono r d K ρ₀ cap rho eta δLoss εInner δglobal ε cLocal cLocal' active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ' hθglobal hspacing' hcc hNum
end Oberwolfach
