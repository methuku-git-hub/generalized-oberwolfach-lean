module

public import Oberwolfach.FirstVortexGlobalThenLocalCallerHierarchy

@[expose] public section
/-! Choose d and K after the ordered matching parameters, retaining the
numeric caller available for each later selector output. -/
set_option autoImplicit false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexCallerParametersChosen
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
    ∀dExtra:ℕ,∃d:ℕ,dExtra≤d ∧ 3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
    ∃ζret ζlocal ηBalance κaux:ℝ,
      FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux ∧
    ∃N:ℕ,∀KExtra:ℕ,∃K:ℕ,KExtra≤K ∧ 3≤K ∧
      5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ ∧
      ∀eps Δ ξPart:ℝ,0<eps→0≤Δ→Δ≤eps/8→0≤ξPart→ξPart≤ξCap→
        3*eps≤lam*(θ/(100*(K:ℝ)^2))→
      ∃ hδ:0<δglobal, ∃ hθ:0<θ, ∃ hθδ:10*θ≤δglobal, ∃ hspacing:1/(d:ℝ)≤θ/1024,
        FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
          ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing

theorem first_vortex_caller_parameters_chosen
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap:ℝ)
    (h:FirstVortexPackingWithCallerBudgets r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap):
    FirstVortexCallerParametersChosen r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap :=by
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθCap,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hCap,dMin,hD⟩:=h
  refine ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθCap,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hCap,?_⟩
  intro dExtra
  obtain ⟨hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,KMin,N,hK⟩:=hD (max dMin dExtra) (le_max_left _ _)
  refine ⟨max dMin dExtra,le_max_right _ _,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,?_⟩
  intro KExtra
  obtain ⟨hK3,hcutHost,hNumeric,hSelectorNumeric⟩:=hK (max KMin KExtra) (le_max_left _ _)
  exact ⟨max KMin KExtra,le_max_right _ _,hK3,hcutHost,hNumeric,hSelectorNumeric⟩
end Oberwolfach
