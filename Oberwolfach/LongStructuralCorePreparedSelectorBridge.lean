module

public import Oberwolfach.LongPreparedSelectorCommonProbability

@[expose] public section
/-! Reorder the actual structural-core event while retaining the expanded,
    stable, reserve-specific and boundary-relative tests on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_structural_core_prepared_selector_bridge
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (Bsmall Bpart:ℕ) (hB:Bsmall≤Bpart)
    (gammaLoss sigmaLoss ξClass Δ:ℝ)
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
    (Prior Parent Expanded Stable Correction ReserveSpecific Relative:
      MarkedExpandedActualOutcome (U:=U) π d→Prop) (bProb:ℝ):
    let Good:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
      LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w
    let Concrete:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
      LongEveryReserveConcreteClassEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
        θ Dv a γ eps βList F hF weight w
    let Boundary:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)
    let Prepared:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
      LongEveryReservePreparedClassesEvent P π d r Dv mm β ε Q Bpart gammaLoss sigmaLoss ξClass Δ z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
    let Other:=fun z=>Prior z ∧ Expanded z ∧ Stable z ∧ ReserveSpecific z ∧ Relative z;
    bProb≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ ReserveSpecific z ∧ Concrete z ∧ Boundary z) ∧ Relative z)→
    bProb≤μ.probability (fun z=>((Other z ∧ Boundary z) ∧ Prepared z) ∧ Concrete z ∧ Parent z ∧
      (True ∧ LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K Bsmall θ Dv a γ eps βList F hF weight w) ∧ Correction z) :=by
  intro Good Concrete Boundary Prepared Other hcore
  have hin:bProb≤μ.probability (fun z=>Other z ∧ Parent z ∧ True ∧ Correction z ∧ Good z ∧ Concrete z ∧ Boundary z):=by
    apply hcore.trans
    apply finiteLaw_probability_mono
    intro z hz
    rcases hz with ⟨⟨hp,hparent,hexp,hstable,hcorr,hgood,hres,hconcrete,hboundary⟩,hrelative⟩
    exact ⟨⟨hp,hexp,hstable,hres,hrelative⟩,hparent,True.intro,hcorr,hgood,hconcrete,hboundary⟩
  exact long_prepared_selector_common_probability P π d r Dv mm β ε Q Bsmall Bpart hB gammaLoss sigmaLoss ξClass Δ
    θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM BO ξSeed ΔSeed ζret ζselect terr τerr
    F hF weight w hPrepared μ Other Parent (fun _=>True) Correction bProb hin
end Oberwolfach
