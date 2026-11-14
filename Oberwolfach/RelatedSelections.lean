module

public import Oberwolfach.FixedCoordinateCounts

@[expose] public section

/-! Fixing coordinates and requiring one additional coordinate to be
related to another reduces the number of free choices by one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000 in
theorem related_fixed_selections_card {I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq I] [Nonempty X]
    (R : X → X → Prop) (q : ℕ) (hR : ∀ x, Fintype.card {y // R x y} ≤ q)
    (A : Finset I) (a : I → X) (i j : I) (hi : i ∉ A) (hij : i ≠ j) :
    Fintype.card {f : I → X // (∀ k ∈ A, f k = a k) ∧ R (f j) (f i)} ≤
      q * Fintype.card X ^ (Fintype.card I - A.card - 1) := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let G := {g : I → X // ∀ k ∈ insert i A, g k = Function.update a i x₀ k}
  let B := {f : I → X // (∀ k ∈ A, f k = a k) ∧ R (f j) (f i)}
  let g (f : B) : G := ⟨Function.update f.1 i x₀, by
    intro k hk
    rcases Finset.mem_insert.mp hk with h | h
    · subst k
      simp
    · have hki : k ≠ i := by intro he; exact hi (he ▸ h)
      simp only [Function.update_of_ne hki]
      exact f.2.1 k h⟩
  let F (f : B) : Σ g : G, {x : X // R (g.1 j) x} :=
    ⟨g f, f.1 i, by simpa only [g, Function.update_of_ne hij.symm] using f.2.2⟩
  have hF : Function.Injective F := by
    intro f f' he
    have hg : g f = g f' := congrArg Sigma.fst he
    have hv : f.1 i = f'.1 i := congrArg (fun z : (Σ g : G, {x : X // R (g.1 j) x}) => z.2.1) he
    apply Subtype.ext
    funext k
    by_cases hk : k = i
    · simpa only [hk] using hv
    · have hh := congrArg (fun z : G => z.1 k) hg
      simpa only [g, Function.update_of_ne hk] using hh
  calc
    Fintype.card B ≤ Fintype.card (Σ g : G, {x : X // R (g.1 j) x}) :=
      Fintype.card_le_of_injective F hF
    _ = ∑ g : G, Fintype.card {x : X // R (g.1 j) x} := Fintype.card_sigma
    _ ≤ ∑ _g : G, q := Finset.sum_le_sum (fun g _ => hR (g.1 j))
    _ = Fintype.card G * q := by simp
    _ = _ := by
      rw [show Fintype.card G = Fintype.card X ^ (Fintype.card I - (insert i A).card) from
        fixedCoordinates_card (insert i A) (Function.update a i x₀)]
      rw [Finset.card_insert_of_notMem hi]
      have hsub : Fintype.card I - (A.card + 1) = Fintype.card I - A.card - 1 := by omega
      rw [hsub, Nat.mul_comm]

end Oberwolfach
