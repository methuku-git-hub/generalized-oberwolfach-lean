module

public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section
/-! Separate an anchored finite weighted sum into supported and excluded
parts, without changing the coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_supported_partition {I:Type} [Fintype I]
    (anchor good:I→Prop) (w:I→ℝ):
    (∑i,if anchor i then w i else 0)=
      (∑i:{i // good i},if anchor i.val then w i.val else 0)+
      (∑i,if anchor i ∧ ¬good i then w i else 0):=by
  have hh:=Fintype.sum_subtype_add_sum_subtype good (fun i=>if anchor i then w i else 0)
  have hb:(∑i:{i // ¬good i},if anchor i.val then w i.val else 0)=
      ∑i,if anchor i ∧ ¬good i then w i else 0:=by
    symm
    calc
      _ = ∑i:{i // ¬good i},if anchor i.val ∧ ¬good i.val then w i.val else 0:=by
        have hx:=finite_sum_restrict_of_zero (fun i=>¬good i)
          (fun i=>if anchor i ∧ ¬good i then w i else 0) (by
            intro i hi
            simp [hi])
        convert hx using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
      _ = _:=by
        apply Finset.sum_congr rfl
        intro i _
        simp only [i.property,not_false_eq_true,and_true]
  rw [hb] at hh
  exact hh.symm
end Oberwolfach
