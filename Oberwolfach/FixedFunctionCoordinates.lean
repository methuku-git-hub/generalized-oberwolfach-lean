module

public import Oberwolfach.FiniteFibreCounts

@[expose] public section

/-! Specifying one value of a finite function leaves exactly one fewer
free coordinate. This is an exact count, including empty codomains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_function_fixed_value_card {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    (i : I) (v : V) :
    Fintype.card {f : I → V // f i=v}=Fintype.card V^(Fintype.card I-1) := by
  let e : {f : I → V // f i=v} ≃ ({j : I // j≠i} → V) := {
    toFun f := fun j => f.val j.val
    invFun g := ⟨fun j => if h : j=i then v else g ⟨j,h⟩,by simp⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext j
      by_cases h : j=i
      · subst j;simp [f.property]
      · simp [h]
    right_inv := by intro g;funext j;simp [j.property] }
  simpa only [Fintype.card_fun,Fintype.card_subtype_compl,Fintype.card_unique] using Fintype.card_congr e

end Oberwolfach
