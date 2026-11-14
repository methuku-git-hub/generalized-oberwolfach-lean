module

public import Oberwolfach.FiniteSupportCounts

@[expose] public section

/-! Sum over a finite subset, split by an explicit predicate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_subset_ite_sum {V A : Type*} [Semiring A]
    (E : Finset V) (P : V → Prop) (a b : A) :
    (∑ e : E,if P e.val then a else b)=
      ((E.filter P).card:A)*a+((E.filter (fun e => ¬P e)).card:A)*b := by
  rw [← Finset.sum_subtype (F:=inferInstance) (p:=fun e => e∈E) E (fun _ => Iff.rfl)
    (fun e => if P e then a else b)]
  simp only [Finset.sum_ite,Finset.sum_const,nsmul_eq_mul]

end Oberwolfach
