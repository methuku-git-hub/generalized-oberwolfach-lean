module

public import Oberwolfach.CanonicalTupleWeights

@[expose] public section

/-! Positional loads of a transversal cycle weighting are the interface
degrees. This is an exact identity before any averaging or deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem left_coordinate_marginal {Ω X Y : Type*} [Fintype Ω] [Fintype Y]
    (f : Ω → X × Y) (w : Ω → ℝ) (x : X) :
    (∑ y, ∑ ω, if f ω = (x,y) then w ω else 0) =
      ∑ ω, if (f ω).1 = x then w ω else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  cases he : f ω with
  | mk a b =>
    by_cases h : a = x <;> simp [he, h]

theorem right_coordinate_marginal {Ω X Y : Type*} [Fintype Ω] [Fintype X]
    (f : Ω → X × Y) (w : Ω → ℝ) (y : Y) :
    (∑ x, ∑ ω, if f ω = (x,y) then w ω else 0) =
      ∑ ω, if (f ω).2 = y then w ω else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  cases he : f ω with
  | mk a b =>
    by_cases h : b = y <;> simp [he, h]

theorem canonical_cyclic_position_loads {k : ℕ} {X : Type*} [Fintype X]
    (L : Fin (k + 2) → X → X → Prop)
    (w : (Fin (k + 2) → X × X) → ℝ)
    (hl : ∀ i x y, (∑ v, if v i = (x,y) then w v else 0) = interfaceCapacity (L i) x y)
    (i : Fin (k + 2)) (x : X) :
    (∑ v, if (v i).1 = x then w v else 0) =
      ((Finset.univ.filter (L i x)).card : ℝ) ∧
    (∑ v, if (v i).2 = x then w v else 0) =
      ((Finset.univ.filter (fun y => L i y x)).card : ℝ) := by
  constructor
  · rw [← left_coordinate_marginal (fun v => v i) w x]
    simp only [hl, interfaceCapacity, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  · rw [← right_coordinate_marginal (fun v => v i) w x]
    simp only [hl, interfaceCapacity, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]

end Oberwolfach
