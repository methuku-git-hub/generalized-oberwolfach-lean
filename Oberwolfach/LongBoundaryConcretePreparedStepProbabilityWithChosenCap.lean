module

public import Oberwolfach.LongBoundaryPreparedCallbackWithChosenCap
public import Oberwolfach.LongBoundaryPreparedNumericCapChoice
public import Oberwolfach.LongStructuralCoreUniversalReservePreparedStepProbability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longConcreteProbabilityCapFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_boundary_concrete_prepared_step_probability_with_chosen_cap
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ζret:ℝ) (d K r:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε)
    (hlamAssign:lam<lamAssign) (hδmargin:δold<δlocal)
    (htiny:lam<((ρ₀/4)/40000)*θ/4096) (hδ:0<δold) (hδ1:δold≤1) (hθ:0<θ) (hepsPos:0<eps)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (hρ₀hi:ρ₀≤1) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hprecise:ε≤((ρ₀/4)/40000)/8192)
    (hlamθ:lam≤θ) (hdlarge:(r+4)+2≤d)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n):
    ∃ξCap:ℝ,0<ξCap ∧ ∀ξPart:ℝ,ξPart≤ξCap → ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hεα:ε≤α/1000) (hlamhi:lam≤α/128)
    (a γ ρ Δ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hρEq:ρ=θ/4096) (hΔeps:Δ≤eps/8)
    (hξSeed:ξSeed≤ξ) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (ζselect:ℝ) (hζselect:ζselect≤ζret) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr),
    ∀(L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra gammaStep sigmaStep:ℝ)
      (hγStep:gammaLoss+extra≤gammaStep) (hσStep:sigmaLoss+extra≤sigmaStep)
      (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
      (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
      (Prior Parent Expanded Stable Correction Good Concrete Relative:
        MarkedExpandedActualOutcome (U:=U) π d→Prop) (b:ℝ),
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ LongCorrectionUniversalMatchingReserveEvent P π d r Dv mm β ε Vort L a₀ b₀ e₀
        gammaLoss sigmaLoss extra ξPart Δ z θ a γ eps βList F hF weight w F₀ ∧
      Concrete z ∧ FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Vort.extendedVertices 1)) ∧ Relative z)→
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ Concrete z ∧ Relative z) ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Vort θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Vort.extendedVertices 1) ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Vort gammaLoss sigmaLoss ξPart Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal α bmatch ρ₀ ξ F hF weight w
        (fun z D₀ C=>LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξPart z (Vort.extendedVertices 1)
          K θ Dv a γ eps βList F hF weight w D₀ C ∧
          LongCorrectedStepDeletionAtReserve P π d r Dv mm β ε Vort gammaStep sigmaStep z D₀ C)) :=by
  obtain ⟨ξCap,hξCap,hbase⟩:=long_boundary_prepared_callback_with_chosen_cap
    α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ζret d K r
    hα hlam hε hlamAssign hδmargin htiny hδ hδ1 hθ hepsPos hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi
    hlamlocal hspacing hd hK hm heps hξ hξ0 hρ₀hi hδglobal hθglobal hprecise hlamθ hdlarge Nret hNret
  refine ⟨ξCap,hξCap,?_⟩
  intro ξPart hξPart
  obtain ⟨N,hbase⟩:=hbase ξPart hξPart
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass
    hcut hcutHost hnoshort hεα hlamhi a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0
    τ Asrc BM hBM weight hw BO hBO w hw0 hwupper ζselect hζselect βList terr τerr hτerr
    L a₀ b₀ e₀ gammaLoss sigmaLoss extra gammaStep sigmaStep hγStep hσStep F₀ μ Prior Parent Expanded Stable Correction Good Concrete Relative b hprob
  have hPrepared:=hbase n hn U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass
    hcut hcutHost hnoshort hεα hlamhi a γ ρ Δ ξSeed ΔSeed haEq hγEq hρEq hΔeps hξSeed hΔSeed heps1 hζ hζ0
    τ Asrc BM hBM weight hw BO hBO w hw0 hwupper ζselect hζselect (Vort.extendedVertices 1) βList terr τerr hτerr gammaLoss sigmaLoss
  exact long_structural_core_universal_reserve_prepared_step_probability P π d r Dv mm β ε Vort L a₀ b₀ e₀
    gammaLoss sigmaLoss extra gammaStep sigmaStep ξPart Δ hγStep hσStep
    θ a γ eps βList lamAssign δlocal δglobal α bmatch ρ₀ ξ BM BO ξSeed ΔSeed ζret ζselect terr τerr
    F hF weight w hPrepared F₀ μ Prior Parent Expanded Stable Correction Good Concrete Relative b hprob
end Oberwolfach
