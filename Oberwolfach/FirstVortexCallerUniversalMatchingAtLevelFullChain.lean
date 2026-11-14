module

public import Oberwolfach.FirstVortexCallerUniversalMatchingAtLevel
public import Oberwolfach.FirstVortexCallerUniversalMatchingAtParentFullChain
public import Oberwolfach.FirstVortexSelectorUniversalMatchingAtLevelFullChain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

def FirstVortexCallerUniversalMatchingAtLevelFullChain
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((γRich/2)*kstar) tstar/128)
    (αHost:ℝ) (hαHost:0<αHost) (hεHost:ε≤αHost/100000)
    (hm:7≤(r+4)) (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ)) (bmatch cTarget ρreserve εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected:ℝ):Prop :=
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
      (∀eps Δ ξPart:ℝ,0<eps→0≤Δ→Δ≤eps/8→0≤ξPart→ξPart≤ξCap→
        3*eps≤lam*(θ/(100*(K:ℝ)^2))→
      ∃ hδ:0<δglobal, ∃ hθ:0<θ, ∃ hθδ:10*θ≤δglobal, ∃ hspacing:1/(d:ℝ)≤θ/1024,
        FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
          ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing) ∧
      ∃(hK3:3≤K) (hθpos:0<θ) (hθ100:θ≤1/100) (hd2:2≤d) (hζret:0<ζret)
        (hlam:0<lam) (hlamθ:lam≤θ) (hξCap:0<ξCap)
        (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ),
      ∀(rPart:ℝ) (hrPart:0<rPart)
        (cBoundary:ℝ) (hcBoundary:0<cBoundary) (hBoundary:4/(d:ℝ)≤cBoundary)
        (BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i),
      FirstVortexSelectorUniversalMatchingAtLevelFullChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
        cap rho eta δLoss εInner δglobal cLocal active lamAssign ηBalance κPack βfinal
        ε hε hε1 hεAbs hεRob hεsmall αHost rPart ζret hαHost hrPart hζret hεHost
        K hK3 hm θ hθpos hθ100 htstarBound d hd2 cBoundary hcBoundary hBoundary hcut BM hBM BO hBO lam hlam hlamθ ξCap hξCap α δold δlocal bmatch cTarget ρreserve κaux εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected

theorem first_vortex_caller_universal_matching_at_level_full_chain
    (r h k₀ Qpow:ℕ) (αRef sstar ω γRich tstar kstar ρ₀:ℝ) (hρ₀:0<ρ₀)
    (β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((γRich/2)*kstar) tstar/128)
    (αHost:ℝ) (hαHost:0<αHost) (hεHost:ε≤αHost/100000)
    (hm:7≤r+4) (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ)) (bmatch cTarget ρreserve:ℝ)
    (εBalSelected ζBalSelected δParentSelected:ℝ)
    (γLevelSelected σLevelSelected κmaxSelected:ℝ)
    (hγLevel:0<γLevelSelected) (hσLevel:0<σLevelSelected) (hκmax:0<κmaxSelected)
    (hCaller:FirstVortexCallerUniversalMatchingAtParentFullChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap
      hε hε1 hεAbs hεRob hεsmall αHost hαHost hεHost hm htstarBound bmatch cTarget ρreserve εBalSelected ζBalSelected δParentSelected):
    FirstVortexCallerUniversalMatchingAtLevelFullChain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
      β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap
      hε hε1 hεAbs hεRob hεsmall αHost hαHost hεHost hm htstarBound bmatch cTarget ρreserve εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected :=by
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθCap,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hCap,hD⟩:=hCaller
  refine ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθCap,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hCap,?_⟩
  intro dExtra
  obtain ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,hK⟩:=hD dExtra
  refine ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,?_⟩
  intro KExtra
  obtain ⟨K,hKExtra,hK3,hcutHost,hNumeric,hNumFor,hK3',hθ',hθ100,hd2,hζret,hlam',hlamθ',hξ',hcut',hSelect⟩:=hK KExtra
  refine ⟨K,hKExtra,hK3,hcutHost,hNumeric,hNumFor,hK3',hθ',hθ100,hd2,hζret,hlam',hlamθ',hξ',hcut',?_⟩
  intro rPart hrPart cBoundary hcBoundary hBoundary BM hBM BO hBO
  have hSel:=hSelect rPart hrPart cBoundary hcBoundary hBoundary BM hBM BO hBO
  exact first_vortex_selector_universal_matching_at_level_full_chain r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
    β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    cap rho eta δLoss εInner δglobal cLocal active lamAssign ηBalance κPack βfinal
    ε hε hε1 hεAbs hεRob hεsmall αHost rPart ζret hαHost hrPart hζret hεHost
    K hK3' hm θ hθ' hθ100 htstarBound d hd2 cBoundary hcBoundary hBoundary hcut' BM hBM BO hBO lam hlam' hlamθ' ξCap hξ'
    α δold δlocal bmatch cTarget ρreserve κaux εBalSelected ζBalSelected δParentSelected γLevelSelected σLevelSelected κmaxSelected hγLevel hσLevel hκmax hSel
end Oberwolfach
