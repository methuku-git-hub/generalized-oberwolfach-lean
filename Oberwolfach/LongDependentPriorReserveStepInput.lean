module

public import Oberwolfach.LongCorrectionReserveUniversalDependentPrior
public import Oberwolfach.LongStructuralUniversalReserveStepExtendedContinuation
public import Oberwolfach.FiniteLawDependentPriorReassociate

@[expose] public section
/-! The dependent-prior correction-and-matching event feeds the reserve step
on the same full outcome without another probability loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_dependent_prior_reserve_step_input
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (θ a γ eps βList ρ₀ BM:ℝ) (BO:Fin K→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    {R:MarkedExpandedActualOutcome (U:=U) π d→Type} [∀z,Fintype (R z)]
    (F₀:(Σz,R z)→Finset (Finset (Fin n)⊕(Fin n×U))) (μ:FiniteLaw (Σz,R z))
    (E:(Σz,R z)→Prop)
    (Prior Parent Expanded Stable Correction Good Concrete Relative:
      MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (hprior:∀x,E x→Prior x.1 ∧ Parent x.1 ∧ Expanded x.1 ∧ Stable x.1 ∧ Concrete x.1 ∧
      FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr x.1 (Q.extendedVertices 1) ∧ Relative x.1)
    (b:ℝ):
    b≤μ.probability (fun x=>((E x ∧ Correction x.1) ∧ Good x.1) ∧
      LongCorrectionReserveUniversalEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
        gammaLoss sigmaLoss extra ξClass Δ x.1 θ a γ eps βList F hF weight w (F₀ x))→
    b≤μ.probability (fun x=>E x ∧ (let z:=x.1;
      (Prior z ∧ Parent z ∧ Expanded z ∧ Stable z ∧ Correction z ∧ Good z ∧
      LongCorrectionReserveUniversalEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
        gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w (F₀ x) ∧
      Concrete z ∧ FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
        a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1)) ∧ Relative z)) :=by
  intro hprob
  exact finiteLaw_dependent_prior_reassociate μ E (fun x=>Correction x.1) (fun x=>Good x.1)
    (fun x=>LongCorrectionReserveUniversalEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ x.1 θ a γ eps βList F hF weight w (F₀ x))
    (fun x=>Prior x.1) (fun x=>Parent x.1) (fun x=>Expanded x.1) (fun x=>Stable x.1)
    (fun x=>Concrete x.1) (fun x=>FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr x.1 (Q.extendedVertices 1))
    (fun x=>Relative x.1) hprior b hprob
end Oberwolfach
