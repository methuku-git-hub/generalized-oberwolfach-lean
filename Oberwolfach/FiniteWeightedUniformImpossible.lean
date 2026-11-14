module

public import Oberwolfach.FiniteWeightedUniformUnion

@[expose] public section
/-! A value excluded by the anchor does not contribute to a finite bad-event
union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_uniform_union_excluding_value {I J K:Type} [Fintype I] [DecidableEq J] [DecidableEq K]
    (S:Finset J) (T:Finset K) (anchor:I→Prop) (f:I→J) (bad:I→K→Prop) (w:I→ℝ) (L:ℝ)
    (hw:∀i,0≤w i) (havoid:∀i,anchor i→f i∉S)
    (hT:∀k∈T,(∑i,if anchor i ∧ bad i k then w i else 0)≤L):
    (∑i,if anchor i ∧ (f i∈S ∨ ∃k∈T,bad i k) then w i else 0)≤(T.card:ℝ)*L:=by
  have he:=finite_weighted_drop_impossible anchor (fun i=>f i∈S) (fun i=>∃k∈T,bad i k) w havoid
  have hh:=finite_weighted_uniform_union T anchor bad w L hw hT
  calc
    _ = ∑i,if anchor i ∧ ∃k∈T,bad i k then w i else 0:=by
      convert he using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    _ ≤ _:=hh
end Oberwolfach
