module

public import Oberwolfach.SeparatedPhysicalPositionBounds

@[expose] public section
/-! The fixed physical-cycle weighting, extended by zero to all ordered
vertex tuples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

def physicalOrdinaryTupleWeight (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ) (C:Fin (n+2)→V):ℝ:=
  if h:PermutationSeparated π b C then separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) ⟨C,h⟩ else 0

theorem physicalOrdinaryTupleWeight_of_separated (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ)
    (C:SeparatedTuple π b (n+2)):
    physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val=separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C:=by
  simp [physicalOrdinaryTupleWeight,C.property]

theorem physicalOrdinaryTupleWeight_nonneg (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀ C,0≤w C)
    (C:Fin (n+2)→V):0≤physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C:=by
  unfold physicalOrdinaryTupleWeight separatedOrderedWeight
  split_ifs <;> first | exact hw _ | exact le_refl _

theorem physicalOrdinaryTupleWeight_upper (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ) (B:ℝ) (hB:0≤B)
    (hb:∀ C,w C≤B/(Fintype.card V:ℝ)^n) (C:Fin (n+2)→V):
    physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C≤B/(Fintype.card V:ℝ)^n:=by
  unfold physicalOrdinaryTupleWeight separatedOrderedWeight
  split_ifs <;> first | exact hb _ | positivity

theorem physicalOrdinaryTupleWeight_support (hn:1≤n) (w:OrdinaryCycle P (n+2)→ℝ)
    (C:Fin (n+2)→V) (h:physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C≠0):
    PermutationSeparated π b C ∧ ∀ i,P.Adj (C i) (C (cycleNext i)):=by
  by_cases hs:PermutationSeparated π b C
  · refine ⟨hs,?_⟩
    apply separatedOrderedWeight_supported hn (fun H=>w (separatedHostCycleToOrdinary H)) ⟨C,hs⟩
    simpa [physicalOrdinaryTupleWeight,hs] using h
  · exact False.elim (h (by simp [physicalOrdinaryTupleWeight,hs]))
end Oberwolfach
