module

public import Oberwolfach.LongSelectedDeletionReservoirMatching
public import Oberwolfach.MarkedCorrectionSelectReserve

@[expose] public section
/-! Select a terminal reservoir after the actual reference correction and
apply the universal matching event to that same deletion and reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] referenceWitnessFinDecidable

theorem long_selected_correction_choose_reserve_matching
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U) (K B:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (εAbs:ℝ) (heB:e₀≤B):
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e);
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∀D₀:MarkedReferenceDeletion P π d σ,
    D₀.Valid H (r+4) T W (γLoss*n) (σLoss*n)→
    (∀v u,¬(H false v u∧H true v u))→
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z T W K B θ D alpha γ eps βList F hF weight w→
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset;
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false;
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs→
    ∀(Xterm Wprotect:Finset (Fin n)) (Bterm Bprotect:Finset U),
      Xterm.card+Bterm.card≤size→Xterm⊆Wprotect→Bterm⊆Bprotect→T⊆Wprotect→W⊆Bprotect→
      (∀v,π v∈T↔v∈T)→(Wprotect.card:ℝ)≤εAbs*n+f₀→(Bprotect.card:ℝ)≤εAbs*n+f₀→
    ∃C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      Disjoint D₀.removed C.edges ∧ MarkedDeletionAvoidsApproximateMatching P π d z D₀ ∧
      LongNamedFixedAbsorber P π d r σ' H' C.edges Xterm Bterm ∧
      LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξClass z T K θ D alpha γ eps βList F hF weight w D₀ C.edges ∧
    ∃D₂:MarkedReferenceDeletion P π d σ,
      D₂.Valid H (r+4) T W (γLoss*n+e₀) (σLoss*n+e₀) ∧
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges:=by
  intro σ H D₀ hValid hsep hEvery σ' H' E' K' hprop Xterm Wprotect Bterm Bprotect
    hsize hX hZ hT hW hπ hWsize hBsize
  obtain ⟨C,_,hCe,hCr,hCu,hfixed,D₂,hValid2,hremoved,hremain,hDis⟩:=
    marked_correction_select_reserve P π d r size a₀ b₀ e₀ f₀ εAbs σ H T W (γLoss*n) (σLoss*n) e₀
      D₀ hValid hsep hprop Xterm Wprotect Bterm Bprotect hsize hX hZ hT hW hπ (by simpa only [Fintype.card_fin] using hWsize)
      (by simpa only [Fintype.card_fin] using hBsize) ∅ (by simp) (by rfl)
  have hmatch:=hEvery D₀ hValid C (hCe.trans heB) hDis
  have havoid:=marked_actual_sample_deletion_avoids_matching P π d z D₀ hValid.1
  refine ⟨C,hCe,hCr,hCu,hDis,havoid,?_,hmatch,D₂,hValid2,hremoved,hremain⟩
  exact hfixed
end Oberwolfach
