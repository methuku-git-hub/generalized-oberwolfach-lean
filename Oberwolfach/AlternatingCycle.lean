module

public import Oberwolfach.CycleEdgeEnumeration
public import Oberwolfach.CyclicCoordinates
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! The two interfaces at each cyclic index are consecutive edges of a
genuine cycle with twice as many vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def alternatingIndex {k : ℕ} (i : Fin (k + 2)) (b : Fin 2) : Fin ((k + 2) * 2) :=
  finProdFinEquiv (i, b)

theorem alternatingIndex_injective {k : ℕ} :
    Function.Injective (fun p : Fin (k + 2) × Fin 2 => alternatingIndex p.1 p.2) :=
  finProdFinEquiv.injective

theorem alternatingIndex_next_zero {k : ℕ} (i : Fin (k + 2)) :
    cycleNext (alternatingIndex i 0) = alternatingIndex i 1 := by
  apply Fin.ext
  rw [cycleNext_val]
  have hi := i.isLt
  change (if 0 + 2 * i.val + 1 < (k + 2) * 2 then 0 + 2 * i.val + 1 else 0) = 1 + 2 * i.val
  split_ifs <;> omega

theorem alternatingIndex_next_one {k : ℕ} (i : Fin (k + 2)) :
    cycleNext (alternatingIndex i 1) = alternatingIndex (finRotate (k + 2) i) 0 := by
  apply Fin.ext
  rw [cycleNext_val, finRotate_apply]
  have hi := i.isLt
  change (if 1 + 2 * i.val + 1 < (k + 2) * 2 then 1 + 2 * i.val + 1 else 0) =
    0 + 2 * ((i.val + 1) % (k + 2))
  by_cases h : i.val + 1 < k + 2
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · have he : i.val + 1 = k + 2 := by omega
    rw [he, Nat.mod_self]
    split_ifs <;> omega

theorem cycleGraph_adj_next {r : ℕ} (hr : 2 ≤ r) (a b : Fin r) :
    (SimpleGraph.cycleGraph r).Adj a b ↔ cycleNext a = b ∨ cycleNext b = a := by
  rw [cycleGraph_modular_adj hr]
  simp only [Fin.ext_iff, cycleNext]

theorem alternatingIndex_eq_iff {k : ℕ} (i j : Fin (k + 2)) (a b : Fin 2) :
    alternatingIndex i a = alternatingIndex j b ↔ i = j ∧ a = b := by
  change finProdFinEquiv (i, a) = finProdFinEquiv (j, b) ↔ _
  rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]

theorem alternatingIndex_adj {k : ℕ} (i j : Fin (k + 2)) (a b : Fin 2) :
    (SimpleGraph.cycleGraph ((k + 2) * 2)).Adj
      (alternatingIndex i a) (alternatingIndex j b) ↔
    (a = 0 ∧ b = 1 ∧ (i = j ∨ i = finRotate (k + 2) j)) ∨
    (a = 1 ∧ b = 0 ∧ (j = i ∨ j = finRotate (k + 2) i)) := by
  rw [cycleGraph_adj_next (by omega)]
  fin_cases a <;> fin_cases b <;>
    simp [alternatingIndex_next_zero, alternatingIndex_next_one, alternatingIndex_eq_iff, eq_comm, or_comm]

def alternatingVertex {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) (i : Fin (k + 2)) (b : Fin 2) :
    (Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y) :=
  if b = 0 then Sum.inl (i, (p i).1) else Sum.inr (i, (p i).2.1)

theorem alternatingVertex_injective {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) :
    Function.Injective (fun t : Fin (k + 2) × Fin 2 => alternatingVertex p t.1 t.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  fin_cases a <;> fin_cases b <;> simp [alternatingVertex] at h ⊢
  all_goals exact h.1

def alternatingCycleEmbedding {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) :
    Fin ((k + 2) * 2) ↪ ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)) :=
  (finProdFinEquiv.symm.toEmbedding).trans
    ⟨fun t => alternatingVertex p t.1 t.2, alternatingVertex_injective p⟩

theorem alternatingCycleEmbedding_apply {k : ℕ} {X Y : Type*}
    (p : Fin (k + 2) → X × Y × X) (i : Fin (k + 2)) (b : Fin 2) :
    alternatingCycleEmbedding p (alternatingIndex i b) = alternatingVertex p i b := by
  simp [alternatingCycleEmbedding, alternatingIndex]

end Oberwolfach
