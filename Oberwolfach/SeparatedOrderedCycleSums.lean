module

public import Oberwolfach.SeparatedOrderedCyclesEquiv
public import Oberwolfach.OrderedCycleAnyPosition

@[expose] public section
/-! Sum over eligible ordered tuples by their physical cycles and
representations, preserving each representation exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

theorem separated_tuple_sum_by_cycle (hn:1≤n) (w:SeparatedHostCycleTuple P π b (n+2)→ℝ):
    (∑ C,w C)=∑ H:SeparatedHostCycle P π b (n+2),∑ f:OrderedCycleRepresentations H.val (n+2),w (separatedSigmaToTuple hn ⟨H,f⟩):=by
  have he:=Equiv.sum_comp (separatedHostCycleTupleEquiv (P:=P) (π:=π) (b:=b) hn).symm w
  rw [Fintype.sum_sigma] at he
  exact he.symm

theorem separated_tuple_cycle_of_representation (hn:1≤n) (H:SeparatedHostCycle P π b (n+2))
    (f:OrderedCycleRepresentations H.val (n+2)):
    separatedTupleCycle hn (separatedSigmaToTuple hn ⟨H,f⟩)=H:=by
  have he:separatedTupleToSigma hn (separatedSigmaToTuple hn ⟨H,f⟩)=⟨H,f⟩:=
    (separatedHostCycleTupleEquiv (P:=P) (π:=π) (b:=b) hn).apply_symm_apply ⟨H,f⟩
  exact congrArg Sigma.fst he
end Oberwolfach
