module

public import Oberwolfach.SeparatedCyclePhysicalWeights

@[expose] public section
/-! The ordered position sums equal the original physical-cycle sums after
removing exactly the cycles that meet the conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

theorem separated_ordered_physical_edge_sum (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ)
    (i:Fin (n+2)) (x y:V):
    (∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
      separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C else 0)=
    ∑ C:OrdinaryCycle P (n+2),if C.val.val.Adj x y ∧ ordinaryCycleSeparatedGood π b C then w C else 0:=by
  have hs:=separatedOrdered_sum_restrict hn (fun H=>w (separatedHostCycleToOrdinary H))
    (fun C:SeparatedTuple π b (n+2)=>C.val i=x ∧ C.val (cycleNext i)=y)
  have hs':(∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
      separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C else 0)=
      (∑ C:SeparatedHostCycleTuple P π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
        w (separatedHostCycleToOrdinary (separatedTupleCycle hn C)) else 0):=by
    convert hs using 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> split_ifs <;> rfl
  rw [hs']
  have ht:=separated_tuple_position_edge_sum (P:=P) (π:=π) (b:=b) hn (fun H=>w (separatedHostCycleToOrdinary H)) i x y
  have ht':(∑ C:SeparatedHostCycleTuple P π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
        w (separatedHostCycleToOrdinary (separatedTupleCycle hn C)) else 0)=
      (∑ H:SeparatedHostCycle P π b (n+2),if H.val.Adj x y then w (separatedHostCycleToOrdinary H) else 0):=by
    convert ht using 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> split_ifs <;> rfl
  rw [ht']
  have hh:=separatedHostCycle_sum_physical (P:=P) (π:=π) (b:=b) (r:=n+2)
    (fun C=>if C.val.val.Adj x y then w C else 0)
  calc
    _ = ∑ H:SeparatedHostCycle P π b (n+2),
        (if (separatedHostCycleToOrdinary H).val.val.Adj x y then w (separatedHostCycleToOrdinary H) else 0):=by
      apply Finset.sum_congr rfl
      intro H _
      split_ifs <;> simp_all [separatedHostCycleToOrdinary]
    _ = _ :=by
      rw [hh]
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> simp_all

theorem separated_ordered_physical_vertex_sum (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ)
    (i:Fin (n+2)) (x:V):
    (∑ C:SeparatedTuple π b (n+2),if C.val i=x then
      separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C else 0)=
    ∑ C:OrdinaryCycle P (n+2),if x∈C.val.val.support ∧ ordinaryCycleSeparatedGood π b C then 2*w C else 0:=by
  have hs:=separatedOrdered_sum_restrict hn (fun H=>w (separatedHostCycleToOrdinary H))
    (fun C:SeparatedTuple π b (n+2)=>C.val i=x)
  have hs':(∑ C:SeparatedTuple π b (n+2),if C.val i=x then
      separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C else 0)=
      (∑ C:SeparatedHostCycleTuple P π b (n+2),if C.val i=x then
        w (separatedHostCycleToOrdinary (separatedTupleCycle hn C)) else 0):=by
    convert hs using 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> split_ifs <;> rfl
  rw [hs']
  have ht:=separated_tuple_position_vertex_sum (P:=P) (π:=π) (b:=b) hn (fun H=>w (separatedHostCycleToOrdinary H)) i x
  have ht':(∑ C:SeparatedHostCycleTuple P π b (n+2),if C.val i=x then
        w (separatedHostCycleToOrdinary (separatedTupleCycle hn C)) else 0)=
      (∑ H:SeparatedHostCycle P π b (n+2),(H.val.degree x:ℝ)*w (separatedHostCycleToOrdinary H)):=by
    convert ht using 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> split_ifs <;> rfl
  rw [ht']
  have hh:=separatedHostCycle_sum_physical (P:=P) (π:=π) (b:=b) (r:=n+2)
    (fun C=>(C.val.val.degree x:ℝ)*w C)
  calc
    _ = ∑ H:SeparatedHostCycle P π b (n+2),
        ((separatedHostCycleToOrdinary H).val.val.degree x:ℝ)*w (separatedHostCycleToOrdinary H):=by rfl
    _ = ∑ C:OrdinaryCycle P (n+2),if ordinaryCycleSeparatedGood π b C then (C.val.val.degree x:ℝ)*w C else 0:=hh
    _ = _ :=by
      apply Finset.sum_congr rfl
      intro C _
      rcases C.val.property.degree_zero_or_two x with hz|ht
      · have hx:x∉C.val.val.support:=(C.val.val.degree_eq_zero_iff_notMem_support x).mp hz
        simp [hz,hx]
      · have hx:x∈C.val.val.support:=(C.val.val.degree_pos_iff_mem_support x).mp (by omega)
        simp [ht,hx]
end Oberwolfach
