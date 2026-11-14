module

public import Oberwolfach.ActualReservedSpokeMatchingLists

@[expose] public section
/-! The exact endpoint-loss bound preserves the linear list size required by
the bad-edge assignment when the original list has the displayed slack. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem actual_reserved_matching_list_lower_bound
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (S:Sym2 V→Finset I)
    (K:SimpleGraph V) (α:ℝ)
    (hS:∀e∈K.edgeFinset,α*Fintype.card V+2*C.card≤((S e).card:ℝ)):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
    (∀e∈K.edgeFinset,∀v∈e.toFinset,∀i∈L e,v∉A i) ∧
    (∀e,L e⊆S e) :=by
  intro A L
  have hh:=actual_reserved_spoke_matching_lists C Hold S
  refine ⟨?_,?_,hh.1⟩
  · intro e he
    have hsize:=hh.2.2.1 e
    have hc:((S e).card:ℝ)≤(L e).card+2*C.card:=by exact_mod_cast hsize
    linarith [hS e he]
  · intro e he v hv i hi
    exact hh.2.1 e v hv i hi
theorem actual_reserved_matching_list_lower_bound_from_double_density
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (S:Sym2 V→Finset I)
    (K:SimpleGraph V) (α:ℝ)
    (hBase:∀e∈K.edgeFinset,2*α*Fintype.card V≤((S e).card:ℝ))
    (hReserve:2*(C.card:ℝ)≤α*Fintype.card V):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
    (∀e∈K.edgeFinset,∀v∈e.toFinset,∀i∈L e,v∉A i) ∧
    (∀e,L e⊆S e) :=by
  apply actual_reserved_matching_list_lower_bound C Hold S K α
  intro e he
  have h:=hBase e he
  nlinarith
end Oberwolfach
