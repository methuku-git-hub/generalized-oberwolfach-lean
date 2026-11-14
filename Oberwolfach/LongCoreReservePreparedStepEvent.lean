module

public import Oberwolfach.LongCoreReservePreparedProbability
public import Oberwolfach.LongCorrectionReserveConcreteClassStepEvent

@[expose] public section
/-! The prepared matching and the level-budget deletion use the same
correction, absorber reserve, and sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

def LongCorrectedStepDeletionAtReserve
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (gammaStep sigmaStep:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))):Prop :=
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∃D₂:MarkedReferenceDeletion P π d σ,
      D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaStep*n) (sigmaStep*n) ∧
      D₂.removed=D₀.removed∪C ∧ D₂.remaining H=D₀.remaining H\C ∧ Disjoint D₀.removed C

theorem long_core_reserve_boundary_prepared_step_event
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
    (z:MarkedExpandedActualOutcome (U:=U) π d) (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hBoundary:FirstVortexConcreteBoundaryEvent P π d r Dv mm β ε Q θ ρ₀ BM BO F hF weight w
      a γ eps Δ ξSeed ΔSeed ζret ζselect βList terr τerr z (Q.extendedVertices 1))
    (hReserve:LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀):
    LongTerminalPreparedChainEvent P π d r Dv mm β ε Q gammaLoss sigmaLoss ξClass Δ e₀ L z
      θ a γ eps βList lamAssign δlocal δglobal αMatch bmatch ρ₀ ξPrep F hF weight w
      (fun z D₀ C=>LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C ∧
        LongConcreteMatchedClassAtReserve P π d r Dv mm β ε Q ξClass Δ z θ a γ eps βList F hF weight w D₀ C ∧
        LongCorrectedStepDeletionAtReserve P π d r Dv mm β ε Q gammaStep sigmaStep z D₀ C) :=by
  have hStep:=long_correction_reserve_concrete_class_step_event P π d r Dv mm β ε Q L a₀ b₀ e₀
    gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ hγStep hσStep z θ a γ eps βList F hF weight w F₀ hReserve
  obtain ⟨D₀,hvalid,havoid,C,hF₀,hcard,hrows,hhubs,hnew,horiginal,hmatching,hconcrete,D₂,hD₂,hremoved,hremain,hdis⟩:=hStep
  have hterm:longTerminalProtectedReserve P π d r z z.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
      gammaLoss sigmaLoss e₀ (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) D₀ C.edges:=by
    simpa only [longTerminalProtectedReserve,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id] using
      (show D₀.Valid _ _ _ _ _ _ ∧ C.edges.card≤e₀ ∧ Disjoint D₀.removed C.edges ∧ _ from
        ⟨hvalid,hcard,hdis,horiginal⟩)
  exact ⟨D₀,C.edges,hterm,hPrepared z hBoundary D₀ C.edges hmatching,hmatching,hconcrete,D₂,hD₂,hremoved,hremain,hdis⟩

end Oberwolfach
