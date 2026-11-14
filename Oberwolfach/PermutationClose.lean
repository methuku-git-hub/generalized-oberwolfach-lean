module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-! Being at cyclic permutation distance at most b is expressed by at
most b forward steps in either direction, including equality. This
works for all cycle lengths, including fixed points. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def PermutationClose {V : Type*} (π : Equiv.Perm V) (b : ℕ) (x y : V) : Prop :=
  x = y ∨ ∃ j : Fin b, (π ^ (j.val + 1)) x = y ∨ (π ^ (j.val + 1)) y = x

theorem permutationClose_symm {V : Type*} (π : Equiv.Perm V) (b : ℕ) (x y : V) :
    PermutationClose π b x y ↔ PermutationClose π b y x := by
  simp only [PermutationClose, eq_comm, or_comm]

theorem permutationClose_neighbour_card {V : Type*} [Fintype V]
    (π : Equiv.Perm V) (b : ℕ) (x : V) :
    Fintype.card {y // PermutationClose π b x y} ≤ 2 * b + 1 := by
  classical
  let A := Finset.univ.image (fun j : Fin b => (π ^ (j.val + 1)) x)
  let B := Finset.univ.image (fun j : Fin b => (π ^ (j.val + 1)).symm x)
  let S := insert x (A ∪ B)
  have hmem (y : V) (h : PermutationClose π b x y) : y ∈ S := by
    rcases h with h | ⟨j, h | h⟩
    · subst y
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      exact ((π ^ (j.val + 1)).eq_symm_apply.mpr h).symm
  let f : {y // PermutationClose π b x y} → S := fun y => ⟨y.1, hmem y.1 y.2⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    exact congrArg (fun w : S => w.val) he
  have ha : A.card ≤ b := (Finset.card_image_le).trans (by simp)
  have hb : B.card ≤ b := (Finset.card_image_le).trans (by simp)
  calc
    _ ≤ Fintype.card S := Fintype.card_le_of_injective f hf
    _ = S.card := Fintype.card_coe S
    _ ≤ (A ∪ B).card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 * b + 1 := by have hh := Finset.card_union_le A B; omega

end Oberwolfach
