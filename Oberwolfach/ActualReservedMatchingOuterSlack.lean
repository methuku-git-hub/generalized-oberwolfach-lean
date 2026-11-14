module

public import Oberwolfach.ActualReservedMatchingAssignmentInputs

@[expose] public section
/-! The original pair lists lie in the outer labels; old images avoid those
labels. Thus the assignment's old-image shielding condition is automatic. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem actual_reserved_matching_inputs_from_outer_slack
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (S:Sym2 V→Finset I)
    (K:SimpleGraph V) (Inner:Finset I) (Old Outer:I→Finset V) (Bad:V→Finset I) (α:ℝ)
    (hSlack:∀e∈K.edgeFinset,α*Fintype.card V+2*C.card≤((S e).card:ℝ))
    (hOutside:∀e∈K.edgeFinset,Disjoint (S e) Inner)
    (hOuter:∀e∈K.edgeFinset,∀i∈S e,∀v∈e.toFinset,v∈Outer i)
    (hOld:∀i,Disjoint (Old i) (Outer i)):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
    (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
    (∀i e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old i→i∈L e→i∈Bad v) ∧
    (∀e∈K.edgeFinset,∀v∈e.toFinset,∀i∈L e,v∉A i) :=by
  intro A L
  have hL:=actual_reserved_matching_list_lower_bound C Hold S K α hSlack
  refine ⟨hL.1,?_,?_,hL.2.1⟩
  · intro e he
    exact Disjoint.mono_left (hL.2.2 e) (hOutside e he)
  · intro i e v he hv ho hi
    have hiS:=hL.2.2 e hi
    exact ((Finset.disjoint_left.mp (hOld i)) ho (hOuter e he i hiS v hv)).elim
end Oberwolfach
