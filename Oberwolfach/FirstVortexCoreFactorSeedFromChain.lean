module

public import Oberwolfach.FirstVortexCoreFactorSeedProbability

@[expose] public section
/-! Attach the checked fixed-reserve factor-seed continuation to the
    structural-core probability event, on the same sample and reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance coreFactorThresholdFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) coreFactorThresholdSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance coreFactorThresholdArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

 theorem first_vortex_core_factor_seed_from_chain_probability
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret:ℝ) (d K r:ℕ)
    (Δ rho δLoss εInner eta:ℝ) (e:ℕ) (cap cLocal active ηBalance κPack βfinal:ℝ) (N:ℕ)
    (hChain:FirstVortexFixedTerminalChainAt α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
      cap cLocal active ηBalance κPack βfinal N)
    (n:ℕ) (hn:N≤n) [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm:ℕ) (β:ℝ) (Q:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed) (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hεα:ε≤α/1000) (hlamhi:lam≤α/128)
    (a γ ξSeed ΔSeed:ℝ)
    (haEq:a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)))
    (hγEq:γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))))
    (hΔeps:Δ≤eps/8) (hξSeed:ξSeed≤ξ) (hΔSeed:Δ≤ΔSeed) (heps1:eps≤1)
    (hζ:ζret≤θ/4096) (hζ0:0≤ζret)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (ζselect βList terr τerr:ℝ) (hζselect:ζselect≤ζret) (hτerr:0≤τerr)
    (γLoss σLoss extra:ℝ) (size a₀ b₀ e₀ f₀ L Bpart:ℕ) (εAbs ζCorr ξCorr:ℝ)
    (hsize:2*mm≤size) (hL:L+1=Q.length)
    (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (hξCorr:0≤ξCorr) (hbudgetCorr:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*n)≤min (γLoss*n) (σLoss*n))
    (heAbs:ε≤εAbs) (heB:e₀≤Bpart)
    (αAssign ρreserve:ℝ) (hαAssign:αAssign/2=α) (hReserveScale:(e₀:ℝ)≤ρreserve*n) (hee:e₀≤e)
    (hU:0<Fintype.card U) (hεδ:ε≤δglobal) (hu:Fintype.card U≤n)
    (hρreserve:0≤ρreserve) (hListMargin:βfinal+2*ρreserve≤βList/2) (hΔξ:Δ≤ξ)
    (h:ℕ) (hh:1≤h) (sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon:ℕ)
    (ρHost:ℝ) (hρHost:0<ρHost) (hsizeHost:ρHost*Dv=2*Fintype.card U)
    (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent:ℝ) (hγRich:0≤γRich)
    (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (κaux κref:ℝ) (hηBalance:0<ηBalance) (hκaux:0<κaux) (hκref:0≤κref) (hκrefCap:κref≤κaux)
    (hεRefEq:εRefEvent=κref/4) (hεNbr0:0≤εNbrEvent) (hεNbrCap:εNbrEvent≤κaux)
    (hκauxCap:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1))) (hκauxRet:κaux≤ζret)
    (εStable ζStable capStable:ℝ) (sizeStable aStable bStable eStable fStable:ℕ) (hζStable:0≤ζStable)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U))) (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Prior Parent Expanded Stable Correction Good Concrete Relative:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hCommon:∀z,Prior z→LongMatchingCommonEvent P π Dv mm β ε Q hπ r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
      F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
      εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
      ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z))
    (hStable:∀z,Stable z→MarkedRetainedRobustChangeEvent P π d r false false εStable ζStable capStable sizeStable aStable bStable eStable fStable (markedExpandedActualSelected π d z))
    (hCorrection:∀z,Correction z→
      let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedMarkedCollapse x (z.1 x)
      let H:=retainedRawMarkedSpokes π d (fun x=>σ (Sum.inr x)) false
        (startRetentionMinimum (rawStartHubSet π d (fun x=>σ (Sum.inr x)) false)) z.2 false false;
      MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζCorr ξCorr σ H
        (Q.extendedVertices 1) (Q.extendedIndices 1))
    (hGood:∀z,Good z→LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξPart z
      (Q.extendedVertices 1) (Q.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w)
    (hPrepared:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξPart z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξPart Δ
        lamAssign δlocal δglobal α bmatch ρ₀ ξ F hF weight w D₀ C)
    (b:ℝ):
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
        γLoss σLoss extra ξPart Δ z θ a γ eps βList F hF weight w F₀ ∧
      Concrete z ∧ FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)) ∧ Relative z)→
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧ Good z ∧ Concrete z ∧ Relative z) ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q γLoss σLoss ξPart Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal α bmatch ρ₀ ξ F hF weight w
        (fun z D₀ C=>(LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξPart z (Q.extendedVertices 1)
          K θ Dv a γ eps βList F hF weight w D₀ C ∧
          LongConcreteMatchedClassAtReserve P π d r Dv mm β ε Q ξPart Δ z θ a γ eps βList F hF weight w D₀ C) ∧
          FirstVortexFixedReserveFactorSeedConclusion P π d r Dv mm β ε Q hπ L e₀ γLoss σLoss
            αAssign lamAssign δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret
            Δ rho eta cLocal κPack ηBalance cap active εStable capStable sizeStable eStable
            a γ βList F hF weight w z Parent (fun _ _=>True) D₀ C)) :=by
  have hSelected:=first_vortex_fixed_terminal_chain_at_selected_sample α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    cap cLocal active ηBalance κPack βfinal N hChain
  have hSeed:=first_vortex_fixed_terminal_chain_factor_seed_at_selected_sample α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    cap cLocal active ηBalance κPack βfinal N hSelected
  intro hprob
  apply long_structural_core_reserve_continuation_probability P π d r Dv mm β ε Q L a₀ b₀ e₀ γLoss σLoss extra ξPart Δ
    θ a γ eps βList lamAssign δlocal δglobal α bmatch ρ₀ ξ BM BO ξSeed ΔSeed ζret ζselect terr τerr F hF weight w hPrepared F₀ μ
    Prior Parent Expanded Stable Correction Good Concrete Relative
    (fun z D₀ C=>FirstVortexFixedReserveFactorSeedConclusion P π d r Dv mm β ε Q hπ L e₀ γLoss σLoss
      αAssign lamAssign δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret
      Δ rho eta cLocal κPack ηBalance cap active εStable capStable sizeStable eStable
      a γ βList F hF weight w z Parent (fun _ _=>True) D₀ C) ?_ b hprob
  intro z hprior hBoundary D₀ C hterm hprep _ _
  obtain ⟨hprior,hparent,hExpanded,hstable,hcorrection,hgood,hConcrete,hRelative⟩:=hprior
  exact first_vortex_fixed_reserve_factor_seed_conclusion α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret d K r Δ rho δLoss εInner eta e
    cap cLocal active ηBalance κPack βfinal N hSeed n hn U P π Dv mm β Q hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    hεα hlamhi a γ (θ/4096) ξSeed ΔSeed haEq hγEq rfl hΔeps hξSeed hΔSeed heps1 hζ hζ0 τ Asrc BM hBM weight hw BO hBO w hw0 hwupper
    z Parent hparent ζselect hζselect (Q.extendedVertices 1) βList terr τerr hτerr hBoundary
    γLoss σLoss size a₀ b₀ e₀ f₀ L Bpart εAbs ζCorr ξCorr hsize hL hπ hξCorr hbudgetCorr heAbs heB (hGood z hgood) (hCorrection z hcorrection)
    (fun _ _=>True) D₀ C hterm trivial hprep αAssign ρreserve hαAssign hReserveScale hee hU hεδ hu hρreserve hListMargin hΔξ
    h hh sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent hγRich levelWeight (hCommon z hprior)
    κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hκauxRet
    εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable (hStable z hstable)
end Oberwolfach
