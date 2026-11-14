module

public import Oberwolfach.TupleRelationDeletionCounts
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! A single fixed coordinate preserves the degree-controlled tuple loss.
Both directions of the deleted relation are required: an edge at the fixed
coordinate can enter or leave that coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

theorem inserted_tuple_relation_deletion_count (D : V → V → Prop)
    (i j k : Fin (m+1)) (hjk : j≠k) (v : V) (d : ℝ)
    (hrow : ∀ x,(∑ y,bipAdj D x y)≤d)
    (hcol : ∀ y,(∑ x,bipAdj D x y)≤d) :
    (∑ z : Fin m → V,if D (Fin.insertNth (α:=fun _=>V) i v z j)
      (Fin.insertNth (α:=fun _=>V) i v z k) then (1:ℝ) else 0)≤
      d*(Fintype.card V:ℝ)^(m-1) := by
  by_cases hj : j=i
  · subst j
    obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
    simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    have hh := tuple_unary_deletion_count (fun y=>D v y) l d (by
      convert hrow v using 1 <;> congr!)
    simpa only [Fintype.card_fin] using hh
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hj
    by_cases hk : k=i
    · subst k
      simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
      have hh := tuple_unary_deletion_count (fun x=>D x v) l d (by
        convert hcol v using 1 <;> congr!)
      simpa only [Fintype.card_fin] using hh
    · obtain ⟨l',rfl⟩ := Fin.exists_succAbove_eq hk
      have hne : l≠l' := fun h=>hjk (congrArg i.succAbove h)
      simp only [Fin.insertNth_apply_succAbove]
      have hh := tuple_relation_deletion_count D l l' hne d hrow
      simpa only [Fintype.card_fin] using hh

end Oberwolfach
