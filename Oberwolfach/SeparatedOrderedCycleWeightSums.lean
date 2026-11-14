module

public import Oberwolfach.SeparatedOrderedCycleSums
public import Oberwolfach.OrderedCyclePositionSums

@[expose] public section
/-! Transfer fixed physical-cycle weights to ordered separated tuples with
the exact edge and vertex multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

theorem separated_tuple_position_edge_sum (hn:1≤n) (w:SeparatedHostCycle P π b (n+2)→ℝ)
    (i:Fin (n+2)) (x y:V):
    (∑ C:SeparatedHostCycleTuple P π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then w (separatedTupleCycle hn C) else 0)=
      ∑ H:SeparatedHostCycle P π b (n+2),if H.val.Adj x y then w H else 0:=by
  rw [separated_tuple_sum_by_cycle hn]
  apply Finset.sum_congr rfl
  intro H _
  calc
    _ = ∑ f:OrderedCycleRepresentations H.val (n+2),if f.val i=x ∧ f.val (cycleNext i)=y then w H else 0:=by
      apply Finset.sum_congr rfl
      intro f _
      have hc:=separated_tuple_cycle_of_representation hn H f
      change (if f.val i=x ∧ f.val (cycleNext i)=y then w (separatedTupleCycle hn (separatedSigmaToTuple hn ⟨H,f⟩)) else 0)=_
      rw [hc]
    _ = _:=orderedCycle_position_edge_sum H.val n hn H.property.1 i x y (w H)

theorem separated_tuple_position_vertex_sum (hn:1≤n) (w:SeparatedHostCycle P π b (n+2)→ℝ)
    (i:Fin (n+2)) (x:V):
    (∑ C:SeparatedHostCycleTuple P π b (n+2),if C.val i=x then w (separatedTupleCycle hn C) else 0)=
      ∑ H:SeparatedHostCycle P π b (n+2),(H.val.degree x:ℝ)*w H:=by
  rw [separated_tuple_sum_by_cycle hn]
  apply Finset.sum_congr rfl
  intro H _
  calc
    _ = ∑ f:OrderedCycleRepresentations H.val (n+2),if f.val i=x then w H else 0:=by
      apply Finset.sum_congr rfl
      intro f _
      have hc:=separated_tuple_cycle_of_representation hn H f
      change (if f.val i=x then w (separatedTupleCycle hn (separatedSigmaToTuple hn ⟨H,f⟩)) else 0)=_
      rw [hc]
    _ = _:=orderedCycle_position_vertex_sum H.val n hn H.property.1 i x (w H)
end Oberwolfach
