module

public import Oberwolfach.LongCoreReservePreparedProbability
public import Oberwolfach.LongStructuralCoreReserveProbability

@[expose] public section
/-! Directly connect the structural core to matching, preparation and the
    terminal absorber on one sample, with its original probability bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_structural_core_reserve_prepared_probability
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra ξClass Δ:ℝ)
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
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Prior Parent Expanded Stable Correction Good Concrete Relative:
      MarkedExpandedActualOutcome (U:=U) π d→Prop) (b:ℝ):
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
        gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀ ∧
      Concrete z ∧ FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)) ∧ Relative z)→
    b≤μ.probability (fun z=>(Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧
      Good z ∧ Concrete z ∧ Relative z) ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1) ∧
      LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
        θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
        (fun z D₀ C=>LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
          K θ Dv a γ eps βList F hF weight w D₀ C ∧
          LongConcreteMatchedClassAtReserve P π d r Dv mm β ε Q ξClass Δ z θ a γ eps βList F hF weight w D₀ C)) :=by
  intro hprob
  let Bdy:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
    FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)
  let Res:=fun z:MarkedExpandedActualOutcome (U:=U) π d=>
    LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀
  let Other:=fun z=>Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧ Good z ∧ Concrete z ∧ Relative z
  have hin:=long_structural_core_reserve_probability μ Prior Parent Expanded Stable Correction Good Res Concrete Bdy Relative b hprob
  exact long_core_reserve_boundary_prepared_probability P π d r Dv mm β ε Q L a₀ b₀ e₀ gammaLoss sigmaLoss extra ξClass Δ
    θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep BM BO ξSeed ΔSeed ζret ζselect terr τerr F hF weight w hPrepared F₀ μ Other b hin
end Oberwolfach
