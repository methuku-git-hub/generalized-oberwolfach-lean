module

public import Oberwolfach.ActualReservedSpokeInnerExclusions

@[expose] public section
/-! The free-image list and the still-unoccupied inner labels exclude the
actual reserved spoke labels by their displayed set definitions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem actual_reservation_canonical_list_exclusions
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop)
    (Outer Y Occupied:I→Finset V) (Inner:Finset V) (InnerIndices:Finset I):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let Reserve:=fun i=>(Outer i∪Y i)∩Inner
    let Lists:=fun i=>Outer i\(Inner∪A i)
    let Required:=fun i=>if i∈InnerIndices then Inner\(Reserve i∪Occupied i) else ∅;
    (∀i,Disjoint (Lists i) (A i)) ∧
    (∀i,Required i⊆Inner\Reserve i) ∧
    (∀i,i∉InnerIndices→Required i=∅) :=by
  intro A Reserve Lists Required
  refine ⟨?_,?_,?_⟩
  · intro i
    apply Finset.disjoint_left.mpr
    intro v hv hA
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ hA)
  · intro i v hv
    by_cases hi:i∈InnerIndices
    · have hh: v∈Inner\(Reserve i∪Occupied i):=by simpa only [Required,hi,↓reduceIte] using hv
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hh).1,fun hR=>(Finset.mem_sdiff.mp hh).2 (Finset.mem_union_left _ hR)⟩
    · simp only [Required,hi,↓reduceIte,Finset.notMem_empty] at hv
  · intro i hi
    simp only [Required,hi,↓reduceIte]
theorem actual_reservation_canonical_assignment_exclusions
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop)
    (Outer Y Occupied Old:I→Finset V) (Inner:Finset V) (InnerIndices:Finset I)
    (hOldOuter:∀i,Disjoint (Old i) (Outer i)) (hOldOccupied:∀i,Old i⊆Occupied i):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let Reserve:=fun i=>(Outer i∪Y i)∩Inner
    let Lists:=fun i=>Outer i\(Inner∪A i)
    let Required:=fun i=>if i∈InnerIndices then Inner\(Reserve i∪Occupied i) else ∅;
    (∀i,Disjoint (Old i) (Required i)) ∧
    (∀i,i∉InnerIndices→Required i=∅) ∧
    (∀i,Disjoint (Lists i) (Old i)) ∧
    (∀i,Disjoint (Lists i) (A i)) ∧
    (∀i,Required i⊆Inner\Reserve i) :=by
  intro A Reserve Lists Required
  have h:=actual_reservation_canonical_list_exclusions C Hold Outer Y Occupied Inner InnerIndices
  refine ⟨?_,h.2.2,?_,h.1,h.2.1⟩
  · intro i
    apply Finset.disjoint_left.mpr
    intro v hOld hRequired
    by_cases hi:i∈InnerIndices
    · have hh:v∈Inner\(Reserve i∪Occupied i):=by simpa only [Required,hi,↓reduceIte] using hRequired
      exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_union_right _ (hOldOccupied i hOld))
    · simp only [Required,hi,↓reduceIte,Finset.notMem_empty] at hRequired
  · intro i
    apply Finset.disjoint_left.mpr
    intro v hList hOld
    exact (Finset.disjoint_left.mp (hOldOuter i)) hOld (Finset.mem_sdiff.mp hList).1
end Oberwolfach
