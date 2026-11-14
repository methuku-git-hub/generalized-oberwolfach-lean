module

public import Oberwolfach.FiniteUniform

@[expose] public section

/-! Exposing the first label of an ordered sample without replacement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def embeddingCons {V : Type*} {r : ℕ} (x : V) (f : Fin r ↪ {y : V // y ≠ x}) : Fin (r + 1) ↪ V where
  toFun := Fin.cons x (fun i => (f i).1)
  inj' := by
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact ((f _).2 hij.symm).elim
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij
      exact ((f _).2 hij).elim
    · simp only [Fin.cons_succ] at hij
      exact congrArg Fin.succ (f.injective (Subtype.ext hij))

def embeddingTail {V : Type*} {r : ℕ} (f : Fin (r + 1) ↪ V) : Fin r ↪ {y : V // y ≠ f 0} where
  toFun i := ⟨f i.succ, fun h => Fin.succ_ne_zero i (f.injective h)⟩
  inj' := by
    intro i j h
    exact Fin.succ_injective _ (f.injective (congrArg Subtype.val h))

def orderedSampleFirstEquiv (V : Type*) (r : ℕ) :
    (Fin (r + 1) ↪ V) ≃ (Σ x : V, Fin r ↪ {y : V // y ≠ x}) where
  toFun f := ⟨f 0, embeddingTail f⟩
  invFun p := embeddingCons p.1 p.2
  left_inv f := by
    ext i
    cases i using Fin.cases <;> rfl
  right_inv := by
    rintro ⟨x, f⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    ext i
    rfl

theorem remainingLabels_card {V : Type*} [Fintype V] (x : V) :
    Fintype.card {y : V // y ≠ x} = Fintype.card V - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem orderedSample_fibre_card {V : Type*} [Fintype V] (r : ℕ) (x : V) :
    Fintype.card (Fin r ↪ {y : V // y ≠ x}) = (Fintype.card V - 1).descFactorial r := by
  rw [Fintype.card_embedding_eq, remainingLabels_card, Fintype.card_fin]

theorem orderedSample_nonempty {V : Type*} [Fintype V] {r : ℕ}
    (hr : r ≤ Fintype.card V) : Nonempty (Fin r ↪ V) :=
  Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hr)

theorem orderedSample_fibre_nonempty {V : Type*} [Fintype V] {r : ℕ}
    (hr : r + 1 ≤ Fintype.card V) (x : V) : Nonempty (Fin r ↪ {y : V // y ≠ x}) := by
  apply orderedSample_nonempty
  rw [remainingLabels_card]
  omega

end Oberwolfach
