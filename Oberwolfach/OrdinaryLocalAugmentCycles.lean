module

public import Oberwolfach.OrdinaryLocalHostAugment

@[expose] public section
/-! Augmenting edges outside the local domain does not change any local
cycle, its vertices, or its physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_augmented_cycle_le (Q F:SimpleGraph V) (T:Finset V)
    (C:LocalOrdinaryCycle (ordinaryLocalHostAugment Q T) F T r):C.val.val.val≤Q:=by
  intro v w hvw
  have hvT:=C.property.1 v hvw.mem_support_left
  have hwT:=C.property.1 w hvw.mem_support_right
  exact (ordinary_local_host_augment_inside Q T v w hvT hwT).mp (C.val.property hvw)

def ordinaryLocalAugmentEquiv (Q F:SimpleGraph V) (T:Finset V):
    LocalOrdinaryCycle Q F T r ≃ LocalOrdinaryCycle (ordinaryLocalHostAugment Q T) F T r where
  toFun:=localOrdinaryRestrictionParent (ordinary_local_host_le_augment Q T) (Finset.Subset.rfl)
  invFun C:=⟨⟨C.val.val,ordinary_local_augmented_cycle_le Q F T C⟩,C.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem ordinary_local_augment_vertices (Q F:SimpleGraph V) (T:Finset V)
    (C:LocalOrdinaryCycle Q F T r):
    localOrdinaryVertices (ordinaryLocalAugmentEquiv Q F T C)=localOrdinaryVertices C:=rfl
end Oberwolfach
