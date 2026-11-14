module

public import Oberwolfach.MarkedWheels

@[expose] public section

/-! Changing one rim label changes only its spoke, in the type determined
by whether that position is the head of the marked arc. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedPositionType {m : ℕ} (i : Fin (m+1)) : Bool := decide (i=0)

theorem markedSpokeIndicator_positions {V : Type*} [DecidableEq V] {m : ℕ}
    (C : Fin (m+1) → V) (j : Bool) (v : V) :
    markedSpokeIndicator C j v=
      ∑ i : Fin (m+1),if markedPositionType i=j then (if C i=v then (1:ℝ) else 0) else 0 := by
  rw [Fin.sum_univ_succ]
  cases j <;> simp [markedSpokeIndicator,markedPositionType]

theorem markedSpokeIndicator_replacement {V : Type*} [DecidableEq V] {m : ℕ}
    (C C' : Fin (m+1) → V) (i : Fin (m+1))
    (h : ∀ k,k≠i → C k=C' k) (j : Bool) (v : V) :
    markedSpokeIndicator C j v-markedSpokeIndicator C' j v=
      if markedPositionType i=j then (if C i=v then (1:ℝ) else 0)-(if C' i=v then 1 else 0) else 0 := by
  rw [markedSpokeIndicator_positions,markedSpokeIndicator_positions,← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · split_ifs <;> ring
  · intro k _ hki
    rw [h k hki,sub_self]
  · simp

end Oberwolfach
