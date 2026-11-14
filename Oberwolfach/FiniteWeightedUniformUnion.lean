module

public import Oberwolfach.FiniteWeightedBadElim

@[expose] public section
/-! Uniform weighted bounds for a union of finitely many bad events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_uniform_union {I J:Type} [Fintype I] [DecidableEq J]
    (S:Finset J) (anchor:I→Prop) (bad:I→J→Prop) (w:I→ℝ) (L:ℝ)
    (hw:∀i,0≤w i) (hbound:∀j∈S,(∑i,if anchor i ∧ bad i j then w i else 0)≤L):
    (∑i,if anchor i ∧ ∃j∈S,bad i j then w i else 0)≤(S.card:ℝ)*L:=by
  have hh:=finite_weighted_bad_union S anchor bad w hw
  calc
    _ ≤ ∑j∈S,∑i,if anchor i ∧ bad i j then w i else 0:=hh
    _ ≤ ∑_j∈S,L:=Finset.sum_le_sum hbound
    _ = _:=by simp

theorem finite_weighted_uniform_double_union {I J K:Type} [Fintype I] [DecidableEq J] [DecidableEq K]
    (S:Finset J) (T:Finset K) (anchor:I→Prop) (bad:I→J→Prop) (other:I→K→Prop)
    (w:I→ℝ) (L:ℝ) (hw:∀i,0≤w i)
    (hS:∀j∈S,(∑i,if anchor i ∧ bad i j then w i else 0)≤L)
    (hT:∀k∈T,(∑i,if anchor i ∧ other i k then w i else 0)≤L):
    (∑i,if anchor i ∧ ((∃j∈S,bad i j) ∨ ∃k∈T,other i k) then w i else 0)≤
      ((S.card:ℝ)+T.card)*L:=by
  have hh:=finite_weighted_two_bad_union anchor (fun i=>∃j∈S,bad i j) (fun i=>∃k∈T,other i k) w hw
  have h1:=finite_weighted_uniform_union S anchor bad w L hw hS
  have h2:=finite_weighted_uniform_union T anchor other w L hw hT
  calc
    _ ≤ (∑i,if anchor i ∧ (∃j∈S,bad i j) then w i else 0)+
        (∑i,if anchor i ∧ (∃k∈T,other i k) then w i else 0):=by
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    _ ≤ (S.card:ℝ)*L+(T.card:ℝ)*L:=add_le_add h1 h2
    _ = _:=by ring
theorem finite_weighted_uniform_value_and_union {I J K:Type} [Fintype I] [DecidableEq J] [DecidableEq K]
    (S:Finset J) (T:Finset K) (anchor:I→Prop) (f:I→J) (other:I→K→Prop)
    (w:I→ℝ) (L:ℝ) (hw:∀i,0≤w i)
    (hS:∀j∈S,(∑i,if anchor i ∧ f i=j then w i else 0)≤L)
    (hT:∀k∈T,(∑i,if anchor i ∧ other i k then w i else 0)≤L):
    (∑i,if anchor i ∧ (f i∈S ∨ ∃k∈T,other i k) then w i else 0)≤
      ((S.card:ℝ)+T.card)*L:=by
  have he (i:I):(∃j∈S,f i=j) ↔ f i∈S:=by
    constructor
    · rintro ⟨j,hj,hij⟩
      simpa only [hij] using hj
    · intro hi
      exact ⟨f i,hi,rfl⟩
  have hh:=finite_weighted_uniform_double_union S T anchor (fun i j=>f i=j) other w L hw (by
    convert hS using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hT
  simp only [he] at hh
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
