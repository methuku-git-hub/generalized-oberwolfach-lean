module

public import Oberwolfach.OrdinaryBoundaryClassDegreeBounds

@[expose] public section
/-! The total number of endpoint-spoke demands is at most the physical
vertex count times the actual maximum physical degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_row_sum_bound
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (D:ℕ)
    (hdeg:∀w:V⊕U,(ordinaryPhysicalGraph Q H).degree w≤D):
    Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H X Z i)≤Fintype.card (V⊕U)*D:=by
  have hrow:∀i,(ordinaryBoundaryRowSet H X Z i).card≤D:=(ordinary_boundary_class_degree_bounds Q H X Z D hdeg).1
  have hcard:Fintype.card {v:V // v∉X}≤Fintype.card (V⊕U):=
    Fintype.card_le_of_injective (fun i:{v:V // v∉X}=>Sum.inl i.val) (by
      intro a b h
      exact Subtype.ext (Sum.inl.inj h))
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i:{v:V // v∉X},D := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using hrow i
    _ = Fintype.card {v:V // v∉X}*D := by simp
    _ ≤ Fintype.card (V⊕U)*D := Nat.mul_le_mul_right D hcard
end Oberwolfach
