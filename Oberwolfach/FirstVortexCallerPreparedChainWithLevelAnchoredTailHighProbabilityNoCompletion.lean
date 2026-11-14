module

public import Oberwolfach.FirstVortexCallerPreparedChainWithHighProbabilityTailNoCompletion
public import Oberwolfach.FirstVortexNamedTailAtMatchingLevelAnchoredHighProbabilityNoCompletion

@[expose] public section
/-! Align the probability tail's host margin, retained sample, and parent
weight tolerance with the prepared matching and level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
local instance callerLevelAnchoredHighProbabilityTailFinNoCompletion (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def FirstVortexCallerPreparedChainWithLevelAnchoredTailHighProbabilityNoCompletion
    (r h k₀ Qpow:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal chainCap localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch:ℝ)
    (αRef sstar ω γRich tstar kstar:ℝ) (hρ₀:0<ρ₀)
    (βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((γRich/2)*kstar) tstar/128)
    (hm:7≤r+4) (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ)) (gammaStep sigmaStep:ℝ):Prop :=
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
      (∃(hθpos:0<θ) (hθone:θ≤1/100) (hK3:3≤K) (hd2:2≤d)
        (hboundary:0<active*ε/320) (hspace:4/(d:ℝ)≤active*ε/320)
        (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ) (hlam:0<lam) (hlamθ:lam≤θ) (hξ:0<ξCap) (hζret:0<ζret),
        ∀(BM:ℝ) (hBM:0<BM) (BO:Fin K→ℝ) (hBO:∀i,0<BO i),
        FirstVortexNamedTailAtMatchingLevelAnchoredHighProbabilityNoCompletion r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
          βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
          ε hε hε1 hεAbs hεRob hεsmall K hK3 hm θ hθpos hθone htstarBound d hd2 (active*ε/320) hboundary hspace hcut
          BM hBM BO hBO lam hlam hlamθ ξCap hξ
          α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret gammaStep sigmaStep κaux) ∧
      ∀eps Δ ξPart:ℝ,0<eps→0≤Δ→Δ≤eps/8→0≤ξPart→ξPart≤ξCap→
        3*eps≤lam*(θ/(100*(K:ℝ)^2))→
      ∃ hδ:0<δglobal, ∃ hθ:0<θ, ∃ hθδ:10*θ≤δglobal, ∃ hspacing:1/(d:ℝ)≤θ/1024,
        FirstVortexActualCallerNumericResult r d K ρ₀ cap rho eta δLoss εInner δglobal
          ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing ∧
        ∀ξPrep:ℝ,0≤ξPrep→4*ξPrep≤eps/2→
    ∀e:ℕ, (∃Nchain:ℕ,FirstVortexFixedTerminalChainAt α lam lamAssign ε δold δlocal δglobal θ eps ξPrep ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
      cap chainCap active ηBalance κPack βfinal Nchain) ∧
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (a γ ρ Δ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hρEq:ρ=θ/4096) (hΔeps:Δ≤eps/8)
    (hξSeed:ξSeed≤ξPrep) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (ζselect:ℝ) (hζselect:ζselect≤ζret) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr) (γLoss σLoss:ℝ),
    ∀z:MarkedExpandedActualOutcome (U:=U) π d,
    FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z Inner →
    ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
      (CReserve:Finset (Finset (Fin n)⊕(Fin n×U))),
    LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξPart z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ CReserve →
    LongBoundaryPreparedClasses P π d r Dv mm β ε Vort z θ a γ eps βList ξPart Δ
      lamAssign δlocal δglobal α bmatch ρ₀ ξPrep F hF weight w D₀ CReserve

theorem first_vortex_caller_prepared_chain_with_level_anchored_tail_high_probability_no_completion
    (r h k₀ Qpow:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal chainCap localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch:ℝ)
    (αRef sstar ω γRich tstar kstar:ℝ) (hρ₀:0<ρ₀)
    (βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεAbs:ε≤εAbs) (hεRob:ε≤εRob)
    (hεsmall:ε≤min ((γRich/2)*kstar) tstar/128)
    (hm:7≤r+4) (htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ)) (gammaStep sigmaStep:ℝ)
    (hαRef:0<αRef) (hεHost:ε≤(2*αRef)/100000) (hkstar:0<kstar)
    (hpstarBound:4*(((r+4):ℕ):ℝ)*kstar≤ρ₀*(1/100))
    (hPrepared:FirstVortexCallerPreparedChainWithHighProbabilityTailNoCompletion r h k₀ Qpow ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal chainCap localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch
      αRef sstar ω γRich tstar kstar hρ₀ βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      hε hε1 hεAbs hεRob hεsmall hm htstarBound gammaStep sigmaStep):
    FirstVortexCallerPreparedChainWithLevelAnchoredTailHighProbabilityNoCompletion r h k₀ Qpow ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal chainCap localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch
      αRef sstar ω γRich tstar kstar hρ₀ βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
      hε hε1 hεAbs hεRob hεsmall hm htstarBound gammaStep sigmaStep:=by
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθUpper,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hClassCap,hD⟩:=hPrepared
  refine ⟨t,s,lamAssign,θ,lam,ξCap,κPack,ht,htCap,hs,hAssign,hAssignCap,hθ,hθs,hθUpper,
    hκ,hκs,hκCap,hθκ,hceiling,hlam,hξ,hlams,hlamCap,hξs,hξCap,hlamθ,hlamα,hlamδ,hClassCap,?_⟩
  intro dExtra
  obtain ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,hK⟩:=hD dExtra
  refine ⟨d,hdExtra,hd3,hdlarge,hspacing,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hRet,N,?_⟩
  intro KExtra
  obtain ⟨K,hKExtra,hK3,hcutHost,hNumeric,hTail,hRest⟩:=hK KExtra
  refine ⟨K,hKExtra,hK3,hcutHost,hNumeric,?_,hRest⟩
  obtain ⟨hθpos,hθone,hK3',hd2,hboundary,hspace,hcut',hlam',hlamθ',hξ',hζret,hFor⟩:=hTail
  have hκaux:0<κaux:=hRet.2.2.2.1
  refine ⟨hθpos,hθone,hK3',hd2,hboundary,hspace,hcut',hlam',hlamθ',hξ',hζret,?_⟩
  intro BM hBM BO hBO
  exact first_vortex_named_tail_at_matching_level_anchored_high_probability_no_completion r h k₀ Qpow αRef sstar ω γRich tstar kstar ρ₀ hρ₀
    βevent βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable
    ε hε hε1 hεAbs hεRob hεsmall K hK3' hm θ hθpos hθone htstarBound d hd2 (active*ε/320) hboundary hspace hcut'
    BM hBM BO hBO lam hlam' hlamθ' ξCap hξ'
    α cLocal chainCap active lamAssign δglobal δold δlocal bmatch ζret ηBalance κPack βfinal cap rho eta δLoss εInner hζret
    gammaStep sigmaStep κaux hαRef hεHost hκaux hkstar hpstarBound (hFor BM hBM BO hBO)
end Oberwolfach
