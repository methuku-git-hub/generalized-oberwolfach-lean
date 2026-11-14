module

public import Oberwolfach.MarkedReferenceStateRemainder
public import Oberwolfach.MarkedFixedTerminalCompletion
public import Oberwolfach.MarkedTerminalCompletionBetweenHosts
public import Oberwolfach.MarkedDeletedHostIncidence

@[expose] public section

/-! Delete a previously constructed wheel-decomposable reservoir from a
fixed reference. The state, its exact physical complement, the two incidence
bounds and canonical divisibility are derived from the actual wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_absorber_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool → V → U → Prop) (X:Finset V) (Y:Finset U) (γ σloss:ℝ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S
    let R:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
    (∀ v u,¬(H false v u∧H true v u)) →
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m →
    ∀ C:Finset (Finset V⊕(V×U)),HasResourceDecomposition R C →
      C.filter (markedInnerResource X Y)=∅ → (C.card:ℝ)≤γ → (C.card:ℝ)≤σloss →
    ∃ D:MarkedReferenceDeletion P π d σ,D.Valid H m X Y γ σloss ∧ D.removed=C ∧ D.remaining H=Full\C := by
  intro E K S Full R hH hDiv C hDec hEmpty hγ hσ
  obtain ⟨M,hM,hMC⟩:=hDec
  let FA:=M.biUnion markedWheelArcs
  let FS:=M.biUnion markedWheelSpokePairs
  let D:MarkedReferenceDeletion P π d σ:=⟨FA,FS⟩
  have hCsub:C⊆Full:=by
    rw [←hMC]
    intro z hz
    obtain ⟨W,hW,hz⟩:=Finset.mem_biUnion.mp hz
    exact marked_wheel_resources_in_full_host _ _ _ _ (H false) (H true) π m (3*d) W hz
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun a=>σ (Sum.inl a))
  have hMS:FA⊆Finset.univ ∧ FS⊆S:=by
    apply marked_packing_resources_contained hp M Finset.univ S
    change M.biUnion markedWheelPhysicalResources⊆Full
    rw [hMC]
    exact hCsub
  have hRemoved:D.removed=C:=by
    change markedFiniteResources _ _ _ _ π (M.biUnion markedWheelArcs) (M.biUnion markedWheelSpokePairs)=C
    rw [markedPackingResources_eq_finite]
    exact hMC
  have hDivRem:MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) (Finset.univ\FA) (S\FS) m:=
    marked_packing_remainder_divisible hH Finset.univ S hDiv M hM hMS.1 hMS.2
  have hCanonical : let σNext:=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ FA).edgeFinset
      let HNext:=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph FS)
      let ENext:=MarkedSampleArc P π (3*d) (fun a=>σNext (Sum.inl a)) false
      let KNext:=MarkedSampleArc P π (3*d) (fun a=>σNext (Sum.inl a)) true;
      MarkedRemainderDivisible (fun e:ENext=>e.val.1) (fun e=>e.val.2)
        (fun e:KNext=>e.val.1) (fun e=>e.val.2) (HNext true) Finset.univ
        (Finset.univ.filter (fun z:V×U=>HNext false z.1 z.2∨HNext true z.1 z.2)) m:=by
    apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
    intro z i
    rw [(marked_canonical_deleted_balance_values P π d m σ H FA FS Finset.univ Finset.univ z i).1]
    exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hDivRem z i
  have hCard (A:Finset (Finset V⊕(V×U))) (hA:A⊆C) (physical:Bool) (z:V⊕U):
      (((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        π (H false) (H true) physical z).filter
        (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈A)).card:ℝ)≤C.card:=by
    let T:=(markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈A)
    let f:=markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true)
    have hi:Function.Injective f:=markedActivePhysical_injective hp
    have hsub:T.image f⊆C:=by
      intro z hz
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hz
      exact hA (Finset.mem_filter.mp ha).2
    exact_mod_cast (show T.card≤C.card from (Finset.card_image_of_injective T hi).symm.trans_le (Finset.card_le_card hsub))
  refine ⟨D,?_,hRemoved,?_⟩
  · change _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨hMS.2,?_,?_,?_,hCanonical⟩
    · simpa only [hRemoved] using hEmpty
    · intro physical z
      rw [hRemoved]
      exact (hCard C (Finset.Subset.refl _) physical z).trans hγ
    · intro physical z
      rw [hRemoved]
      exact (hCard (C.filter (markedStarResource X Y)) (Finset.filter_subset _ _) physical z).trans hσ
  · change Full\D.removed=Full\C
    rw [hRemoved]

end Oberwolfach
