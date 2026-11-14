module

public import Oberwolfach.FirstVortexCallerParametersChosen
public import Oberwolfach.LongBoundaryPreparedSolverFromConcreteEvent

@[expose] public section
/-! Attach the uniform concrete-boundary solver to the exact caller choices,
including the same retention threshold and summed-loss numeric witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance callerPreparedSolverFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def FirstVortexCallerParametersPrepared
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch:ℝ):Prop :=
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
          ε cLocal active θ lamAssign lam eps Δ ξPart ζret ηBalance κPack βfinal hδ hθ hθδ hspacing ∧
        ∀ξPrep:ℝ,0≤ξPrep→4*ξPrep≤eps/2→
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


theorem first_vortex_caller_prepared_solver_same_choices
    (r:ℕ) (ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal:ℝ)
    (α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch:ℝ)
    (hα:0<α) (hε:0<ε) (hδold:0<δold) (hδold1:δold≤1)
    (hρ:0<ρ₀) (hρhi:ρ₀≤1) (hb:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hprecise:ε≤((ρ₀/4)/40000)/8192) (hεalpha:ε≤α/1000)
    (hθUpperOld:θUpper≤δold/32) (hθUpperOne:θUpper≤1/100)
    (hm:7≤r+4)
    (h:FirstVortexCallerParametersChosen r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap):
    FirstVortexCallerParametersPrepared r ρ₀ cap βfinal rho eta ζmax Δmax δLoss εInner δglobal θmax tGlobal
      α ε c cLocal localCap active θUpper assignUpper δold δlocal lamCap κPackCap bmatch :=by
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
  obtain ⟨hδ,hθ',hθglobal,hspacing',hNum⟩:=hSelectorNumeric eps Δ ξPart heps hΔ0 hΔ hξPart0 hξPart hEpsRate
  refine ⟨hδ,hθ',hθglobal,hspacing',hNum,?_⟩
  intro ξPrep hξPrep0 hξPrep
  have hθold:θ≤δold/32:=hθUpper.trans hθUpperOld
  have hθδold:10*θ≤δold:=by linarith
  have hθone:θ≤1/100:=hθUpper.trans hθUpperOne
  obtain ⟨hζret,hζlocal,hηbal,hκaux,hζs,hζc,hζθ,hζloc,hζscale,hηs,hηc,hκs,hκζ,hκbal,Nret,hNret,hLocal⟩:=hRet
  have hNret':∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hNret
  obtain ⟨Nprep,hprep⟩:=long_boundary_prepared_solver_from_concrete_event α lam lamAssign ε δold δlocal δglobal θ eps ξPrep ρ₀ bmatch ξPart ζret d K r
    hα hlam hε hδold hδold1 hθ heps hρ hb hαb hbd hεsmall hθδold hθold hθone hlamδ hspacing hd3 hK3 hm hEpsRate hξPrep hξPrep0
    hρhi hδ hθglobal hprecise ξCap hξPart hClassCap hlamθ hdlarge Nret hNret'
  refine ⟨Nprep,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhiHost hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hnoshort
    a γ ρ Δ' ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper
    ζselect hζselect Inner βList terr τerr hτerr γLoss σLoss
  have hprep':=hprep n hn
  have hdec:longPreparedSolverFin n=callerPreparedSolverFin n:=Subsingleton.elim _ _
  have hdecK:longPreparedSolverFin K=callerPreparedSolverFin K:=Subsingleton.elim _ _
  try rw [hdec] at hprep'
  try rw [hdecK] at hprep'
  have hcut':(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut
  have hcutHost':5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hcutHost
  exact hprep' U P π Dv mm β Vort hreg hDv hρhiHost hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut' hcutHost' hnoshort
    hεalpha hlamα a γ ρ Δ' ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζθ hζret.le τ Asrc BM hBM weight hw BO hBO w hw0 hwupper
    ζselect hζselect Inner βList terr τerr hτerr γLoss σLoss
end Oberwolfach
