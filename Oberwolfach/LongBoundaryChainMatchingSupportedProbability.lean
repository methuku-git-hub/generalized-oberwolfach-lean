module

public import Oberwolfach.LongBoundaryAllReservePreparedProbability
public import Oberwolfach.LongSampleChainReserveEvents
public import Oberwolfach.FiniteLawSupportProbabilityMono
public import Oberwolfach.FirstVortexConcreteBoundaryEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Add prepared-class witnesses for every admissible correction and reserve
without changing the common sample or its probability bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_boundary_chain_matching_from_supported_selector
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (Bpart:ℕ) (gammaLoss sigmaLoss ξClass Δ:ℝ)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM:ℝ)
    (BO:Fin K→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hPrepared:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Prior:MarkedExpandedActualOutcome (U:=U) π d→Prop) (bProb:ℝ)
    (Chain:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))→
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
    (hChain:∀z:MarkedExpandedActualOutcome (U:=U) π d,0<μ.mass z→Prior z→
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w→
      LongSampleChainReserveEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss z Chain)
    (hprob:bProb≤μ.probability (fun z=>Prior z ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w)):
    bProb≤μ.probability (fun z=>Prior z ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongSampleChainMatchingEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w Chain) :=by
  have hgood:=long_boundary_all_reserve_prepared_probability P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ
    θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM BO ξSeed ΔSeed ζret ζselect terr τerr
    F hF weight w hPrepared μ Prior bProb hprob
  apply hgood.trans
  apply finiteLaw_probability_mono_on_support
  intro z hz hzGood
  refine ⟨hzGood.1,hzGood.2.1,?_⟩
  exact long_sample_chain_reserve_add_matching P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
    θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w Chain
    hzGood.2.2.1 hzGood.2.2.2 (hChain z hz hzGood.1 hzGood.2.1 hzGood.2.2.1)
end Oberwolfach
