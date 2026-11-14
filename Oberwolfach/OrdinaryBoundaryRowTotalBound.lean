module

public import Oberwolfach.OrdinaryBoundaryClassBoundaryDegree

@[expose] public section
/-! Bound the total number of remaining outside-root incidences by the
    number of physical vertices times the boundary maximum degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_row_total_bound (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (Dmax:ℕ)
    (hdeg:∀w:V⊕U,(ordinaryBoundaryGraph Q H X Z).degree w≤Dmax):
    Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H X Z i)≤Fintype.card (V⊕U)*Dmax :=by
  have hclass:=ordinary_boundary_class_boundary_degree_bounds Q H X Z Dmax hdeg
  have hrow:∀i:{v:V // v∉X},(ordinaryBoundaryRowSet H X Z i).card≤Dmax:=hclass.1
  have hindex:Fintype.card {v:V // v∉X}≤Fintype.card (V⊕U):=
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
      (Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective)
  rw [Fintype.card_sigma]
  calc
    (∑i:{v:V // v∉X},Fintype.card ↥(ordinaryBoundaryRowSet H X Z i)) ≤
        ∑_i:{v:V // v∉X},Dmax:=by
      apply Finset.sum_le_sum
      intro i _
      simpa using hrow i
    _ = Fintype.card {v:V // v∉X}*Dmax:=by simp
    _ ≤ Fintype.card (V⊕U)*Dmax:=Nat.mul_le_mul_right _ hindex
end Oberwolfach
