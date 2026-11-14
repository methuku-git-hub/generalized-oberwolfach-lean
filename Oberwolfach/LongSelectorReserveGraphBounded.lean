module

public import Oberwolfach.LongReservedSampleRimBound
public import Oberwolfach.LongEveryClassValidDeletionEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_selector_bounded_reserve_graph_before_class
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U) (K B:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hEvery:LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z T W K B θ D alpha γ eps βList F hF weight w):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∀D₀:MarkedReferenceDeletion P π d σ,
      D₀.Valid H (r+4) T W (γLoss*n) (σLoss*n)→
    let Ddeleted:=(markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let σ':=rawMarkedDeleteRims σ Ddeleted
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤B→Disjoint D₀.removed C.edges→
    ∃A:SimpleGraph (Fin n),A=markedResourceRimGraph C.edges ∧
      A≤longPhysicalStateGraph P z.1 {0,1,2,3,4} ∧ A.edgeFinset.card≤B ∧
      LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z T K θ D alpha γ eps βList F hF weight w D₀ C.edges := by
  intro σ H D₀ hvalid Ddeleted σ' E' K' C hcard hdis
  have hBounds:=long_reserved_sample_rim_bounded P π d z.1 Ddeleted B C hcard
  have hdec6:instDecidableEqFin 6=referenceWitnessFinDecidable 6:=Subsingleton.elim _ _
  try rw [hdec6] at hBounds
  have hMatching:=hEvery D₀ hvalid C hcard hdis
  exact ⟨markedResourceRimGraph C.edges,rfl,hBounds.1,hBounds.2,hMatching⟩
end Oberwolfach
