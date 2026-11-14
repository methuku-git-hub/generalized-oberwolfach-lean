module

public import Oberwolfach.OrderedSamples

@[expose] public section

/-! Transposing two possible next labels couples their continuation laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def remainingSwap {V : Type*} [DecidableEq V] (x y : V) :
    {z : V // z ≠ x} ≃ {z : V // z ≠ y} where
  toFun z := ⟨Equiv.swap x y z, fun h => z.2 ((Equiv.swap x y).injective (h.trans (Equiv.swap_apply_left x y).symm))⟩
  invFun z := ⟨Equiv.swap x y z, fun h => z.2 ((Equiv.swap x y).injective (h.trans (Equiv.swap_apply_right x y).symm))⟩
  left_inv z := by apply Subtype.ext; exact Equiv.swap_apply_self x y z
  right_inv z := by apply Subtype.ext; exact Equiv.swap_apply_self x y z

theorem embeddingCons_remainingSwap {V : Type*} [DecidableEq V] {r : ℕ}
    (x y : V) (f : Fin r ↪ {z : V // z ≠ x}) :
    embeddingCons y (f.trans (remainingSwap x y).toEmbedding) =
      (embeddingCons x f).trans (Equiv.swap x y).toEmbedding := by
  ext i
  cases i using Fin.cases
  · simp [embeddingCons]
  · rfl

theorem finiteLaw_uniform_expectation_difference_of_equiv
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]
    (e : Ω ≃ Γ) (X : Ω → ℝ) (Y : Γ → ℝ) {c : ℝ}
    (h : ∀ ω, |X ω - Y (e ω)| ≤ c) :
    |(FiniteLaw.uniform Ω).expectation X - (FiniteLaw.uniform Γ).expectation Y| ≤ c := by
  have hh : (FiniteLaw.uniform Γ).expectation Y =
      (FiniteLaw.uniform Ω).expectation (fun ω => Y (e ω)) := by
    rw [← finiteLaw_uniform_map_equiv e, finiteLaw_map_expectation]
  rw [hh]
  exact finiteLaw_expectation_difference _ _ _ h

theorem embeddingCons_swap_tail {V : Type*} [DecidableEq V] {r : ℕ}
    (x : V) [DecidableEq {z : V // z ≠ x}]
    (u v : {z : V // z ≠ x}) (f : Fin r ↪ {z : V // z ≠ x}) :
    embeddingCons x (f.trans (Equiv.swap u v).toEmbedding) =
      (embeddingCons x f).trans (Equiv.swap u.1 v.1).toEmbedding := by
  ext i
  cases i using Fin.cases
  · change x = Equiv.swap u.1 v.1 x
    exact (Equiv.swap_apply_of_ne_of_ne u.2.symm v.2.symm).symm
  · rename_i j
    change ((Equiv.swap u v) (f j)).1 = Equiv.swap u.1 v.1 (f j).1
    exact (Subtype.val_injective.swap_apply u v (f j)).symm

end Oberwolfach
