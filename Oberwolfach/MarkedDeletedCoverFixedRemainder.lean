module

public import Oberwolfach.MarkedCurrentPackingRemainder
public import Oberwolfach.MarkedFixedReferenceCoverRemainder
public import Oberwolfach.MarkedFiniteResourceSupport
public import Oberwolfach.MarkedFinitePackingIteration

@[expose] public section

/-! The output of cover-down in the actual deleted sample supplies a
balanced remainder on the original occurrence identifiers. The removed
inner resource set and both incidence bounds are measured in the fixed
reference, with no earlier deletion added to the next error set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_deleted_cover_fixed_remainder
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool → V → U → Prop) (hH : ∀ v u,¬(H false v u∧H true v u))
    (I T : Finset V) (J Q : Finset U) (hI : ∀ v,π v∈I↔v∈I) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let B := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S;
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS).filter (markedInnerResource I J)=∅ →
    let DR := markedSampleArcSetGraph P π d σ KA
    let DS := markedFiniteSpokeGraph KS
    let σ' := rawMarkedDeleteRims σ DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S' := Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)
    let B' := markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π Finset.univ S';
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m →
    ∀ M : Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H),
    (∀ Y∈M,∀ Z∈M,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) →
    let AC := Finset.univ\M.biUnion markedWheelArcs
    let SC := S'\M.biUnion markedWheelSpokePairs
    let L := markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π AC SC;
    (∀ a∈AC,Sum.elim (fun e:E'=>e.val.1) (fun e:K'=>e.val.1) a∈I∧
      Sum.elim (fun e:E'=>e.val.2) (fun e:K'=>e.val.2) a∈I) →
    (∀ s∈SC,s.1∈I∧s.2∈J) →
    ∀ γ σloss : ℝ,
    let F := B'.filter (markedInnerResource I J)\L;
    F.filter (markedInnerResource T Q)=∅ →
    (∀ physical x,(((markedIncidentEdges (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) e∈F)).card:ℝ)≤γ) →
    (∀ physical x,(((markedIncidentEdges (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) e∈F.filter (markedStarResource T Q))).card:ℝ)≤σloss) →
    let N := M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H)
    let AR := Finset.univ\(KA∪N.biUnion markedWheelArcs)
    let SR := S\(KS∪N.biUnion markedWheelSpokePairs);
    N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources ∧
    (∀ Y∈N,∀ Z∈N,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
    N.biUnion markedWheelArcs⊆Finset.univ\KA ∧ N.biUnion markedWheelSpokePairs⊆S\KS ∧
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) AR SR m ∧
    (∀ a∈AR,Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈I∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈I) ∧
    (∀ s∈SR,s.1∈I∧s.2∈J) ∧
    markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR=L ∧
    L=B.filter (markedInnerResource I J)\F ∧ F⊆B.filter (markedInnerResource I J) ∧
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F)).card:ℝ)≤γ) ∧
    (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F.filter (markedStarResource T Q))).card:ℝ)≤σloss) := by
  intro E K S B KA KS hEmpty DR DS σ' H' E' K' S' B' hdiv M hM AC SC L hAC hSC γ σloss F hDeep hInc hStar N AR SR
  obtain ⟨hres,hN,hNA,hNS,hdivR,hLR⟩ := marked_current_packing_original_remainder
    P π d m σ H hH KA KS hdiv M hM
  change markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR=L at hLR
  have hLSupport : ∀ e∈L,markedInnerResource I J e :=
    (markedFiniteResources_support_iff _ _ _ _ π AC SC I J hI).mpr ⟨hAC,hSC⟩
  have hLB : L⊆B'.filter (markedInnerResource I J) := by
    intro e he
    exact Finset.mem_filter.mpr ⟨markedFiniteResources_mono Finset.sdiff_subset Finset.sdiff_subset he,hLSupport e he⟩
  obtain ⟨F',hF',hL,hFsub,_,hFI,hFS⟩ := marked_cover_remainder_fixed_reference
    P π d σ H KA KS I T J Q L γ σloss hEmpty hLB hDeep hInc hStar
  change F'=F at hF'
  subst F'
  obtain ⟨hAR,hSR⟩ := (markedFiniteResources_support_iff
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR I J hI).mp
      (by intro e he;exact hLSupport e (hLR ▸ he))
  have hBsub : B'⊆B := by
    have hh : B'=B\markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS := marked_deleted_sample_resources P π d σ H KA KS
    rw [hh];exact Finset.sdiff_subset
  have hFsub' : F⊆B.filter (markedInnerResource I J) := by
    intro e he
    obtain ⟨hB',hin⟩ := Finset.mem_filter.mp (hFsub he)
    exact Finset.mem_filter.mpr ⟨hBsub hB',hin⟩
  exact ⟨hres,hN,hNA,hNS,hdivR,hAR,hSR,hLR,hL,hFsub',hFI,hFS⟩

end Oberwolfach
