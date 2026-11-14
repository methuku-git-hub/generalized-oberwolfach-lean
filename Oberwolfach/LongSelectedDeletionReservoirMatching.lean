module

public import Oberwolfach.LongNamedFixedAbsorber
public import Oberwolfach.LongEveryClassValidDeletionEvent
public import Oberwolfach.MarkedActualSampleMatchingDisjoint

@[expose] public section
/-! The valid deletion selected on an expanded sample can be passed directly
to its universal matching event and the terminal reservoir on that sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] referenceWitnessFinDecidable

theorem long_selected_deletion_reservoir_matching
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U) (K B:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e);
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∀D₀:MarkedReferenceDeletion P π d σ,
    D₀.Valid H (r+4) T W (γLoss*n) (σLoss*n)→
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z T W K B θ D alpha γ eps βList F hF weight w→
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset;
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false;
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
    C.edges.card≤B→Disjoint D₀.removed C.edges→
    ∀(σCorr:RawMarkedOutcome (Fin n) U Bool Bool) (HCorr:Bool→Fin n→U→Prop),
    σCorr=σ'→HCorr=H'→∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))),Reserve=C.edges→
    ∀Xterm:Finset (Fin n),∀Bterm:Finset U,
    LongNamedFixedAbsorber P π d r σCorr HCorr Reserve Xterm Bterm→
    MarkedDeletionAvoidsApproximateMatching P π d z D₀ ∧
    LongNamedFixedAbsorber P π d r σCorr HCorr Reserve Xterm Bterm ∧
    LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z T K θ D alpha γ eps βList F hF weight w D₀ Reserve:=by
  intro σ H D₀ hValid hEvery σ' H' E' K' C hC hDis σCorr HCorr hσCorr hHCorr Reserve hReserve Xterm Bterm hAbs
  subst Reserve
  exact ⟨marked_actual_sample_deletion_avoids_matching P π d z D₀ hValid.1,hAbs,hEvery D₀ hValid C hC hDis⟩
end Oberwolfach
