module

public import Oberwolfach.SeparatedPhysicalPositionSums
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! The manuscript's bounded fractional cycle weights imply the ordered
positional estimates after excluding conflicts, with explicit loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

section
variable (hn:1≤n) (hnV:0<Fintype.card V) (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀ C,0≤w C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,w C≤B/(Fintype.card V:ℝ)^n)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then w C else 0)=if P.Adj x y then 1 else 0)

local notation "W" => (fun H:SeparatedHostCycle P π b (n+2)=>w (separatedHostCycleToOrdinary H))
include hn hnV hw hB hb he

theorem separated_physical_position_edge_error (i:Fin (n+2)) (x y:V)
    (hxy:P.Adj x y) (hclose:¬PermutationClose π b x y):
    |(∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then separatedOrderedWeight hn W C else 0)-1|≤
      5*((n+2:ℕ):ℝ)^4*B*(2*b)/Fintype.card V:=by
  rw [separated_ordered_physical_edge_sum hn w i x y]
  have hdeg:∀ v,((permutationConflictGraph π b).degree v:ℝ)≤2*b:=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π b v
  have hFxy:¬(permutationConflictGraph π b).Adj x y:=fun h=>hclose h.2
  have hh:=ordinary_admissible_cycle_edge_load P (permutationConflictGraph π b) (n+2) (by omega) hnV w hw B hB
    (by simpa using hb) (2*b) hdeg he x y hxy hFxy
  convert hh using 1 <;> congr!

theorem separated_physical_position_vertex_error (i:Fin (n+2)) (x:V):
    |(∑ C:SeparatedTuple π b (n+2),if C.val i=x then separatedOrderedWeight hn W C else 0)-(P.degree x:ℝ)|≤
      6*((n+2:ℕ):ℝ)^4*B*(2*b):=by
  rw [separated_ordered_physical_vertex_sum hn w i x]
  let A:ℝ:=∑ C:OrdinaryCycle P (n+2),if x∈C.val.val.support ∧ ordinaryCycleSeparatedGood π b C then w C else 0
  have hsum:(∑ C:OrdinaryCycle P (n+2),if x∈C.val.val.support ∧ ordinaryCycleSeparatedGood π b C then 2*w C else 0)=2*A:=by
    dsimp [A]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> simp
  rw [hsum]
  have hdeg:∀ v,((permutationConflictGraph π b).degree v:ℝ)≤2*b:=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π b v
  have hh:=ordinary_admissible_cycle_vertex_load P (permutationConflictGraph π b) (n+2) (by omega) hnV w hw B hB
    (by simpa using hb) (2*b) hdeg he x
  have hh':|A-(P.degree x:ℝ)/2|≤3*((n+2:ℕ):ℝ)^4*B*(2*b):=by
    convert hh using 1 <;> congr!
  have hbound:=abs_le.mp hh'
  apply abs_le.mpr
  constructor <;> nlinarith [hbound.1,hbound.2]
end
end Oberwolfach
