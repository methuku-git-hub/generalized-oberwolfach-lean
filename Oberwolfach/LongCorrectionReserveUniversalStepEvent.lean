module

public import Oberwolfach.LongCorrectionUniversalMatchingReserveEvent
public import Oberwolfach.MarkedReferenceDeletionLossMonotone

@[expose] public section
/-! Preserve the same correction, terminal reserve, matching and host while
widening the corrected deletion to independently selected level budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

def LongCorrectionReserveUniversalStepEvent
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ)
    (gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U))):Prop :=
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∃D₀:MarkedReferenceDeletion P π d σ,
      D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n) ∧
      MarkedDeletionAvoidsApproximateMatching P π d z D₀ ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
    let E':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) true;
    ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2) (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      MarkedFixedTerminalAbsorber P π d (r+4) σ' H' C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
      MarkedFixedTerminalAbsorber P π d (r+4) σ H C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
      LongEveryClassMatchingResult Δ P π d r gammaLoss sigmaLoss ξClass z (Q.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C.edges ∧
    ∃D₂:MarkedReferenceDeletion P π d σ,
      D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaStep*n) (sigmaStep*n) ∧
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges

theorem long_correction_reserve_universal_step_event
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ)
    (gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ:ℝ)
    (hγ:gammaLoss+extra≤gammaStep) (hσ:sigmaLoss+extra≤sigmaStep)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (h:LongCorrectionUniversalMatchingReserveEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀):
    LongCorrectionReserveUniversalStepEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ z θ a γ eps βList F hF weight w F₀:=by
  obtain ⟨D₀,hvalid,havoid,C,hF₀,hCe,hCr,hCu,hfixed,horiginal,hmatching,D₂,h₂,hremoved,hremain,hdis⟩:=h
  refine ⟨D₀,hvalid,havoid,C,hF₀,hCe,hCr,hCu,hfixed,horiginal,hmatching,D₂,?_,hremoved,hremain,hdis⟩
  apply marked_reference_deletion_valid_loss_mono D₂ _ (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
    ((gammaLoss+extra)*n) ((sigmaLoss+extra)*n) (gammaStep*n) (sigmaStep*n) ?_ ?_ h₂
  · exact mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg n)
  · exact mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg n)
end Oberwolfach
