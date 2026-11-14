module

public import Oberwolfach.OrdinaryMatchingCycleMassCount

@[expose] public section
/-! A weighted sum over selected, tagged candidates equals the sum of the
class lengths multiplied by their selected counts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem option_matching_mass_by_class
    {C I U:Type} [Fintype I] [DecidableEq I] [DecidableEq U]
    (L:Finset C) (tag:C→Option I) (hub:C→U) (u:U) (i₀:I) (len:I→ℕ):
    (∑x∈L,if (tag x).isSome ∧ hub x=u then len ((tag x).getD i₀) else 0)=
      ∑i:I,((L.filter (fun x=>tag x=some i ∧ hub x=u)).card)*len i:=by
  classical
  calc
    _ = ∑x∈L,∑i:I,if tag x=some i ∧ hub x=u then len i else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      cases ht:tag x with
      | none=>simp [ht]
      | some j=>
        by_cases hh:hub x=u <;> simp [ht,hh]
    _ = ∑i:I,∑x∈L,if tag x=some i ∧ hub x=u then len i else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [←Finset.sum_filter]
      simp
end Oberwolfach
