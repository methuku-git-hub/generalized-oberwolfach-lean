module

public import Oberwolfach.ActualReservedOrdinarySpokeLabels

@[expose] public section
/-! The selected ordinary spoke graph places every reserved ordinary spoke in
the outer list, so the prescribed inner exclusion contains its label. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem actual_reserved_spokes_in_outer_and_inner_exclusion
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (Outer Y:I→Finset V) (Inner:Finset V)
    (hOuter:∀v i,Hold false v i→v∈Outer i):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let Reserve:=fun i=>(Outer i∪Y i)∩Inner;
    (∀i,A i⊆Outer i) ∧ (∀i,A i∩Inner⊆Reserve i) :=by
  intro A Reserve
  have hA:∀i,A i⊆Outer i:=by
    intro i v hv
    exact hOuter v i ((actual_reserved_ordinary_spoke_labels_mem C Hold i v).mp hv).2
  refine ⟨hA,?_⟩
  intro i v hv
  exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hA i (Finset.mem_inter.mp hv).1),
    (Finset.mem_inter.mp hv).2⟩
end Oberwolfach
