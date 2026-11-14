module

public import Oberwolfach.MarkedProtectedCorrectionReferenceState
public import Oberwolfach.MarkedCorrectionAvoidsApproximateMatching

@[expose] public section
/-! A bounded protected correction supplies a valid reference state whose
physical deletion is disjoint from every approximate-layer matching on the
same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem marked_correction_matching_same_sample
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ ξ:ℝ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)))
    (T:Finset V) (W:Finset U) (γ σloss:ℝ) (hξ:0≤ξ)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V)≤min γ σloss):
    let selected:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
    let H:=retainedRawMarkedSpokes π d (fun e=>ω (Sum.inr e)) false t J false false
    let E:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) true
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let R:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξ selected H T W →
    ∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)) (D₀:MarkedReferenceDeletion P π d selected),
      D₀.arcs=DA ∧ D₀.spokes=DS ∧ D₀.Valid H (r+4) T W γ σloss ∧
      (∀ (C:Type) [Fintype C] [DecidableEq C] (Qc:C→Finset R) (M:Finset C),
        Disjoint ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ w))) D₀.removed) ∧
      let σ':=rawMarkedDeleteRims selected (markedSampleArcSetGraph P π d selected DA).edgeFinset
      let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
      let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
      MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs := by
  intro selected t H E K raw R φ hCorr
  obtain ⟨DA,DS,D₀,hDA,hDS,hvalid,hdiv,habs⟩:=
    marked_protected_bounded_correction_reference_state P π d r size a₀ b₀ e₀ f₀ εAbs ζ ξ selected H T W γ σloss hξ hbudget hCorr
  refine ⟨DA,DS,D₀,hDA,hDS,hvalid,?_,habs⟩
  intro C _ _ Qc M
  have hsub:DS⊆Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2):=by
    simpa only [hDS] using hvalid.1
  have hh:=marked_correction_disjoint_from_approximate_matching P π d ω false true (by decide) t J false true (by decide) C Qc M DA DS hsub
  simpa only [MarkedReferenceDeletion.removed,hDA,hDS] using hh

/-- Every selected-layer reference deletion avoids every matching in the
approximate layer of the same expanded sample. -/
theorem marked_reference_deletion_avoids_approximate_matching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false))):
    let selected:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
    let H:=retainedRawMarkedSpokes π d (fun e=>ω (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let R:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀ (D₀:MarkedReferenceDeletion P π d selected),
      D₀.spokes⊆Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2) →
      ∀ (C:Type) [Fintype C] [DecidableEq C] (Qc:C→Finset R) (M:Finset C),
        Disjoint ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ w))) D₀.removed := by
  intro selected t H raw R φ D₀ hsub C _ _ Qc M
  have hh:=marked_correction_disjoint_from_approximate_matching P π d ω false true (by decide) t J false true (by decide)
    C Qc M D₀.arcs D₀.spokes hsub
  simpa only [MarkedReferenceDeletion.removed] using hh
end Oberwolfach
