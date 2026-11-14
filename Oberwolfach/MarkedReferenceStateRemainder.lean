module

public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues
public import Oberwolfach.MarkedFinitePackingIteration

@[expose] public section

/-! Recover the divisible typed remainder of a valid reference-deletion
state in the original occurrence identifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

namespace MarkedReferenceDeletion
variable {P:SimpleGraph V} {π:Equiv.Perm V} {d:ℕ} {σ:RawMarkedOutcome V U Γ Color}

theorem remaining_eq (D:MarkedReferenceDeletion P π d σ) (H:Bool → V → U → Prop):
    D.remaining H=markedFiniteResources
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2) π
      (Finset.univ\D.arcs) ((Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\D.spokes):=by
  exact (markedFiniteResources_sdiff _ _ _ _ π (markedSampleArc_physical_injective P π (3*d) _)
    Finset.univ D.arcs _ D.spokes).symm

theorem removed_subset (D:MarkedReferenceDeletion P π d σ) (H:Bool → V → U → Prop)
    (m:ℕ) (X:Finset V) (Y:Finset U) (γ σloss:ℝ) (h:D.Valid H m X Y γ σloss):
    D.removed⊆markedFiniteResources
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)):=
  markedFiniteResources_mono (Finset.subset_univ _) h.1

theorem original_remainder_divisible (D:MarkedReferenceDeletion P π d σ) (H:Bool → V → U → Prop)
    (m:ℕ) (X:Finset V) (Y:Finset U) (γ σloss:ℝ) (h:D.Valid H m X Y γ σloss):
    MarkedRemainderDivisible
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2) (H true)
      (Finset.univ\D.arcs) ((Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\D.spokes) m:=by
  apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
  intro z i
  rw [←(marked_canonical_deleted_balance_values P π d m σ H D.arcs D.spokes Finset.univ Finset.univ z i).1]
  exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr h.2.2.2.2 z i

end MarkedReferenceDeletion
end Oberwolfach
