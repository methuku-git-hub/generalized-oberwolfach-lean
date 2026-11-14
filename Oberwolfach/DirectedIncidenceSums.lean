module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic

@[expose] public section

/-! Count each directed rim incidence once, retaining incoming and
outgoing incidences as distinct occurrences. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 abbrev DirectedIncidence {E V:Type} (tail head:E→V) (v:V):=
    {e:E // head e=v}⊕{e:E // tail e=v}

 def directedIncidenceEdge {E V:Type} {tail head:E→V} {v:V}:
    DirectedIncidence tail head v→E:=Sum.elim Subtype.val Subtype.val

 theorem finite_function_fiber_sum {E V:Type} [Fintype E] [Fintype V]
    (f:E→V) (g:E→ℤ):
    (∑ v,∑ e:{e:E // f e=v},g e.val)=∑ e,g e:=by
  have h:=Equiv.sum_comp (Equiv.sigmaFiberEquiv f) g
  rw [Fintype.sum_sigma] at h
  exact h

 theorem directed_incidence_sum {E V:Type} [Fintype E] [Fintype V]
    (tail head:E→V) (g:E→V→ℤ):
    (∑ v,∑ i:DirectedIncidence tail head v,g (directedIncidenceEdge i) v)=
      ∑ e,(g e (head e)+g e (tail e)):=by
  simp only [Fintype.sum_sum_type,directedIncidenceEdge,Sum.elim_inl,Sum.elim_inr,Finset.sum_add_distrib]
  have hi:(∑ v,∑ e:{e:E // head e=v},g e.val v)=∑ e,g e (head e):=by
    have h:(∑ v,∑ e:{e:E // head e=v},g e.val v)=∑ v,∑ e:{e:E // head e=v},g e.val (head e.val):=by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro e he
      rw [e.property]
    rw [h]
    exact finite_function_fiber_sum head (fun e=>g e (head e))
  have ho:(∑ v,∑ e:{e:E // tail e=v},g e.val v)=∑ e,g e (tail e):=by
    have h:(∑ v,∑ e:{e:E // tail e=v},g e.val v)=∑ v,∑ e:{e:E // tail e=v},g e.val (tail e.val):=by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro e he
      rw [e.property]
    rw [h]
    exact finite_function_fiber_sum tail (fun e=>g e (tail e))
  rw [hi,ho]

end Oberwolfach
