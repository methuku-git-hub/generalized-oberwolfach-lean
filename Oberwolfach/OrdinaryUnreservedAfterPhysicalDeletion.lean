module

public import Oberwolfach.OrdinaryUnreservedPackingCertificate

@[expose] public section
/-! Deleting an earlier physical packing and then the inner pair and reserve
is the same unreserved host as deleting the union of the physical packings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_after_physical_deletion (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (C R:SimpleGraph (V⊕U)):
    ordinaryUnreservedRim (Q\C.comap Sum.inl) X R=ordinaryUnreservedRim Q X (C⊔R) ∧
    ordinaryUnreservedSpokes (fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u)) X Z R=
      ordinaryUnreservedSpokes H X Z (C⊔R):=by
  constructor
  · ext v w
    simp only [ordinaryUnreservedRim,SimpleGraph.sdiff_adj,spanningRestriction_adj,SimpleGraph.comap_adj,SimpleGraph.sup_adj]
    tauto
  · funext v u
    apply propext
    simp only [ordinaryUnreservedSpokes,SimpleGraph.sup_adj]
    tauto
end Oberwolfach
