module

public import Oberwolfach.ActualReservedMatchingListLowerBound

@[expose] public section
/-! Pass the reserved-spoke-safe lists to the existing bad-edge assignment,
retaining its size, inner-index and occupied-image conditions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem actual_reserved_matching_assignment_inputs
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (S:Sym2 V→Finset I)
    (K:SimpleGraph V) (Inner:Finset I) (Old:I→Finset V) (Bad:V→Finset I) (α:ℝ)
    (hBase:∀e∈K.edgeFinset,2*α*Fintype.card V≤((S e).card:ℝ))
    (hReserve:2*(C.card:ℝ)≤α*Fintype.card V)
    (hOutside:∀e∈K.edgeFinset,Disjoint (S e) Inner)
    (hShield:∀i e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old i→i∈S e→i∈Bad v):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
    (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
    (∀i e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old i→i∈L e→i∈Bad v) ∧
    (∀e∈K.edgeFinset,∀v∈e.toFinset,∀i∈L e,v∉A i) :=by
  intro A L
  have hL:=actual_reserved_matching_list_lower_bound_from_double_density C Hold S K α hBase hReserve
  refine ⟨hL.1,?_,?_,hL.2.1⟩
  · intro e he
    exact Disjoint.mono_left (hL.2.2 e) (hOutside e he)
  · intro i e v he hv ho hi
    exact hShield i e v he hv ho (hL.2.2 e hi)
end Oberwolfach
