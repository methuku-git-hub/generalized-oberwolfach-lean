module

public import Oberwolfach.ResidualActualReservedMatchingContinuation

@[expose] public section
/-! The required labels at inner indices are exactly the inner labels that
are neither reserved, selected, absorber labels, nor already occupied. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [DecidableEq I] [DecidableEq V]

def innerRequiredTargets (inner:Finset I) (vertices:Finset V)
    (reserved selected absorber occupied:I→Finset V) (w:I):Finset V:=
  if w∈inner then vertices\(reserved w∪selected w∪absorber w∪occupied w) else ∅

theorem inner_required_targets_properties
    (inner:Finset I) (vertices:Finset V)
    (reserved selected absorber occupied:I→Finset V):
    (∀w,w∉inner→innerRequiredTargets inner vertices reserved selected absorber occupied w=∅) ∧
    (∀w,innerRequiredTargets inner vertices reserved selected absorber occupied w⊆vertices) ∧
    (∀w,Disjoint (occupied w) (innerRequiredTargets inner vertices reserved selected absorber occupied w)) ∧
    (∀w,Disjoint (absorber w) (innerRequiredTargets inner vertices reserved selected absorber occupied w)) ∧
    (∀w,Disjoint (reserved w) (innerRequiredTargets inner vertices reserved selected absorber occupied w)) ∧
    (∀w,(innerRequiredTargets inner vertices reserved selected absorber occupied w).card≤vertices.card):=by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w hw; simp [innerRequiredTargets,hw]
  · intro w x hx
    by_cases hw:w∈inner
    · simp only [innerRequiredTargets,hw,if_true,Finset.mem_sdiff] at hx;exact hx.1
    · simp [innerRequiredTargets,hw] at hx
  · intro w;apply Finset.disjoint_left.mpr;intro x hx hy
    by_cases hw:w∈inner
    · simp only [innerRequiredTargets,hw,if_true,Finset.mem_sdiff,Finset.mem_union] at hy
      exact hy.2 (Or.inr hx)
    · simp [innerRequiredTargets,hw] at hy
  · intro w;apply Finset.disjoint_left.mpr;intro x hx hy
    by_cases hw:w∈inner
    · simp only [innerRequiredTargets,hw,if_true,Finset.mem_sdiff,Finset.mem_union] at hy
      exact hy.2 (Or.inl (Or.inr hx))
    · simp [innerRequiredTargets,hw] at hy
  · intro w;apply Finset.disjoint_left.mpr;intro x hx hy
    by_cases hw:w∈inner
    · simp only [innerRequiredTargets,hw,if_true,Finset.mem_sdiff,Finset.mem_union] at hy
      exact hy.2 (Or.inl (Or.inl (Or.inl hx)))
    · simp [innerRequiredTargets,hw] at hy
  · intro w;apply Finset.card_le_card
    intro x hx
    by_cases hw:w∈inner
    · simp only [innerRequiredTargets,hw,if_true,Finset.mem_sdiff] at hx;exact hx.1
    · simp [innerRequiredTargets,hw] at hx
end Oberwolfach
