module

public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues

@[expose] public section
/-! A protected sparse correction gives a valid reference state from the
corrected remainder's divisibility, without assuming the original sample is divisible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_correction_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ σloss:ℝ):
    let E:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ (FA:Finset (E⊕K)) (FS:Finset (V×U)),
    FS⊆S →
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π FA FS).filter (markedInnerResource X Y)=∅ →
    (∀ physical z,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun a=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) a∈
          markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π FA FS)).card:ℝ)≤min γ σloss) →
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (H true) (Finset.univ\FA) (S\FS) m →
    ∃ D:MarkedReferenceDeletion P π d σ, D.arcs=FA ∧ D.spokes=FS ∧ D.Valid H m X Y γ σloss := by
  intro E K S FA FS hFS hprotect hinc hdiv
  let D:MarkedReferenceDeletion P π d σ:=⟨FA,FS⟩
  refine ⟨D,rfl,rfl,?_⟩
  change FS⊆S ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hFS,hprotect,?_,?_,?_⟩
  · intro physical z; exact (hinc physical z).trans (min_le_left _ _)
  · intro physical z
    have hh:=hinc physical z
    have hsubset:((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun a=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) a∈D.removed.filter (markedStarResource X Y))) ⊆
      ((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun a=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) a∈D.removed)):=by
      intro a ha; simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1,ha.2.1⟩
    have hcard:=Finset.card_le_card hsubset
    exact (by exact_mod_cast hcard : _ ≤ _).trans (hh.trans (min_le_right _ _))
  · apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
    intro z i
    rw [(marked_canonical_deleted_balance_values P π d m σ H FA FS Finset.univ Finset.univ z i).1]
    exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hdiv z i
end Oberwolfach
