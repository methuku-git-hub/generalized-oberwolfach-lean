module

public import Oberwolfach.LongDependentPriorReserveStepInput
public import Oberwolfach.LongUniversalReserveEventConversion

@[expose] public section
/-! Add any proved pointwise continuation to the same correction and reserve
    selected by the structural core, without losing probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_structural_core_universal_reserve_step_from_dependent_prior_probability
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ:ℝ)
    (hγStep:gammaLoss+extra≤gammaStep) (hσStep:sigmaLoss+extra≤sigmaStep)
    (θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM:ℝ)
    (BO:Fin K→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hPrepared:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C)
    {R:MarkedExpandedActualOutcome (U:=U) π d→Type} [∀z,Fintype (R z)]
    (F₀:(Σz,R z)→Finset (Finset (Fin n)⊕(Fin n×U)))
    (μ:FiniteLaw (Σz,R z)) (E:(Σz,R z)→Prop)
    (Prior Parent Expanded Stable Correction Good Concrete Relative:
      MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hprior:∀x,E x→Prior x.1 ∧ Parent x.1 ∧ Expanded x.1 ∧ Stable x.1 ∧ Concrete x.1 ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr x.1 (Q.extendedVertices 1) ∧ Relative x.1)
    (Continue:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))→
      Finset (Finset (Fin n)⊕(Fin n×U))→Prop)
    (hContinue:∀z:MarkedExpandedActualOutcome (U:=U) π d,
      (Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧ Good z ∧ Concrete z ∧ Relative z)→
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
        (C:Finset (Finset (Fin n)⊕(Fin n×U))),
      longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
        gammaLoss sigmaLoss e₀ (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) D₀ C→
      LongBoundaryPreparedClasses P π d r Dv mm β ε Q z θ a γ eps βList ξClass Δ
        lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w D₀ C→
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C→
      Continue z D₀ C) (b:ℝ):
    b≤μ.probability (fun x=>((E x ∧ Correction x.1) ∧ Good x.1) ∧
      LongCorrectionReserveUniversalEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
        gammaLoss sigmaLoss extra ξClass Δ x.1 θ a γ eps βList F hF weight w (F₀ x))→
    b≤μ.probability (fun x=>E x ∧ (let z:=x.1;
      (Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧ Good z ∧ Concrete z ∧ Relative z) ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
        (fun z D₀ C=>(LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
          K θ Dv a γ eps βList F hF weight w D₀ C) ∧
          Continue z D₀ C ∧ Disjoint C (F₀ x) ∧ LongCorrectedStepDeletionAtReserve P π d r Dv mm β ε Q gammaStep sigmaStep z D₀ C))) :=by
  intro hprob
  have hinput:=long_dependent_prior_reserve_step_input P π d r Dv mm β ε Q L a₀ b₀ e₀
    gammaLoss sigmaLoss extra ξClass Δ θ a γ eps βList ρ₀ BM BO ξSeed ΔSeed ζret ζselect terr τerr
    F hF weight w F₀ μ E Prior Parent Expanded Stable Correction Good Concrete Relative hprior b hprob
  exact long_structural_core_universal_reserve_step_continuation_extended_probability P π d r Dv mm β ε Q L a₀ b₀ e₀
    gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ hγStep hσStep
    θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM BO ξSeed ΔSeed ζret ζselect terr τerr
    F hF weight w hPrepared F₀ μ E Prior Parent Expanded Stable Correction Good Concrete Relative Continue hContinue b hinput
end Oberwolfach
