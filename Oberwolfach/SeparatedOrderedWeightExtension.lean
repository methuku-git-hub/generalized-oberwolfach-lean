module

public import Oberwolfach.SeparatedOrderedCycleWeightSums
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section
/-! Extend the ordered weighting by zero outside the host without changing
its values or introducing representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

abbrev SeparatedTuple (π:Equiv.Perm V) (b r:ℕ):={C:Fin r→V // PermutationSeparated π b C}

def separatedHostTupleNestedEquiv:
    {C:SeparatedTuple π b (n+2) // ∀ i,P.Adj (C.val i) (C.val (cycleNext i))}≃SeparatedHostCycleTuple P π b (n+2) where
  toFun C:=⟨C.val.val,C.val.property,C.property⟩
  invFun C:=⟨⟨C.val,C.property.1⟩,C.property.2⟩
  left_inv C:=by cases C;rfl
  right_inv C:=by cases C;rfl

def separatedOrderedWeight (hn:1≤n) (w:SeparatedHostCycle P π b (n+2)→ℝ)
    (C:SeparatedTuple π b (n+2)):ℝ:=
  if h:∀ i,P.Adj (C.val i) (C.val (cycleNext i)) then w (separatedTupleCycle hn ⟨C.val,C.property,h⟩) else 0

theorem separatedOrderedWeight_supported (hn:1≤n) (w:SeparatedHostCycle P π b (n+2)→ℝ)
    (C:SeparatedTuple π b (n+2)) (h:separatedOrderedWeight hn w C≠0):
    ∀ i,P.Adj (C.val i) (C.val (cycleNext i)):=by
  by_contra hP
  apply h
  simp [separatedOrderedWeight,hP]

theorem separatedOrdered_sum_restrict (hn:1≤n) (w:SeparatedHostCycle P π b (n+2)→ℝ)
    (T:SeparatedTuple π b (n+2)→Prop):
    (∑ C:SeparatedTuple π b (n+2),if T C then separatedOrderedWeight hn w C else 0)=
      ∑ C:SeparatedHostCycleTuple P π b (n+2),if T ⟨C.val,C.property.1⟩ then w (separatedTupleCycle hn C) else 0:=by
  let Q:=fun C:SeparatedTuple π b (n+2)=>∀ i,P.Adj (C.val i) (C.val (cycleNext i))
  letI:DecidablePred Q:=fun C=>Classical.propDecidable (Q C)
  let f:=fun C:SeparatedTuple π b (n+2)=>if T C then separatedOrderedWeight hn w C else 0
  have hz:∀ C,¬Q C→f C=0:=by intro C hC;simp [Q,f,separatedOrderedWeight,hC]
  have hh:=finite_sum_restrict_of_zero Q f hz
  calc
    _ = ∑ C:SeparatedTuple π b (n+2),f C:=by rfl
    _ = ∑ C:{C:SeparatedTuple π b (n+2) // Q C},f C.val:=hh
    _ = _ := by
      rw [←Equiv.sum_comp separatedHostTupleNestedEquiv]
      apply Finset.sum_congr rfl
      intro C _
      have hC:∀ i,P.Adj (C.val.val i) (C.val.val (cycleNext i)):=C.property
      simp [f,separatedOrderedWeight,Q,separatedHostTupleNestedEquiv,hC]
end Oberwolfach
