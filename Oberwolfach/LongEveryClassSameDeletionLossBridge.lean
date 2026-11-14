module

public import Oberwolfach.LongEveryClassValidDeletionEvent
public import Oberwolfach.MarkedReferenceDeletionLossMonotone

@[expose] public section
/-! Keep the actual correction fixed while matching uses a smaller initial
loss budget and the subsequent level chain uses a larger one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_every_class_same_deletion_loss_bridge
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γsmall σsmall γlarge σlarge ξClass:ℝ) (hγ:γsmall≤γlarge) (hσ:σsmall≤σlarge)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n)) (W:Finset U)
    (K B:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hEvent:LongEveryClassValidDeletionEvent Δ P π d r γsmall σsmall ξClass z T W K B θ D alpha γ eps βList F hF weight w)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    D₀.Valid H (r+4) T W (γsmall*n) (σsmall*n)→
    D₀.Valid H (r+4) T W (γlarge*n) (σlarge*n) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤B→Disjoint D₀.removed C.edges→
      LongEveryClassMatchingResult Δ P π d r γlarge σlarge ξClass z T K θ D alpha γ eps βList F hF weight w D₀ C.edges :=by
  intro σ H hValid
  have hγn:γsmall*n≤γlarge*n:=mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg n)
  have hσn:σsmall*n≤σlarge*n:=mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg n)
  refine ⟨marked_reference_deletion_valid_loss_mono D₀ H (r+4) T W _ _ _ _ hγn hσn hValid,?_⟩
  intro σ' E' K' C hcard hdis
  have hmatch:=hEvent D₀ hValid C hcard hdis
  exact hmatch
end Oberwolfach
