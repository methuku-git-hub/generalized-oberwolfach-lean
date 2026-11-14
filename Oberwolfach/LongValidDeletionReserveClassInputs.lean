module

public import Oberwolfach.LongSelectorReserveGraphBounded
public import Oberwolfach.LongFixedAbsorberSelectedRim

@[expose] public section
/-! The selected valid-deletion event and supported reserve provide the
class-matching result and bounds for the actual reserve graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_valid_deletion_reserve_class_inputs
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (γLoss σLoss ξClass:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ eps Δ a γ βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Bpart:ℕ)
    (hEvery:LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∀D₀:MarkedReferenceDeletion P π d σ,
      D₀.Valid H (r+4) (Vort.extendedVertices 1) (Vort.extendedIndices 1) (γLoss*n) (σLoss*n)→
    let Ddeleted:=(markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let σ':=rawMarkedDeleteRims σ Ddeleted
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤Bpart→Disjoint D₀.removed C.edges→
      (∀v,(markedResourceRimGraph C.edges).degree v≤Bpart) ∧
      markedResourceRimGraph C.edges≤longPhysicalStateGraph P z.1 {0,1,2,3,4} ∧
      LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z (Vort.extendedVertices 1)
        K θ Dv a γ eps βList F hF weight w D₀ C.edges :=by
  intro σ H D₀ hvalid Ddeleted σ' E' K' C hcard hdis
  obtain ⟨A,hAeq,hAsample,hAcard,hClass⟩:=long_selector_bounded_reserve_graph_before_class Δ P π d r γLoss σLoss ξClass z
    (Vort.extendedVertices 1) (Vort.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w hEvery D₀ hvalid C hcard hdis
  have hAdeg:∀v,(markedResourceRimGraph C.edges).degree v≤Bpart:=by
    intro v
    rw [←hAeq]
    exact (A.degree_le_card_edgeFinset v).trans hAcard
  have hSample:markedResourceRimGraph C.edges≤longPhysicalStateGraph P z.1 {0,1,2,3,4}:=by
    simpa only [hAeq] using hAsample
  exact ⟨hAdeg,hSample,hClass⟩
end Oberwolfach
