module

public import Oberwolfach.SeparatedWeightRestriction

@[expose] public section

/-! The close-pair counting bound transferred to the paired-coordinate
representation used by the actual cyclic weight construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pairWeightOnLabels {I V : Type*} (w : (I → V × V) → ℝ) (f : I ⊕ I → V) : ℝ :=
  w (fun i => (f (Sum.inl i),f (Sum.inr i)))

def separatedPairWeight {I V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (w : (I → V × V) → ℝ) (t : I → V × V) : ℝ :=
  if PermutationSeparated π b (pairTupleLabels t) then w t else 0

theorem pairWeightOnLabels_incidence {I V : Type*}
    [Fintype I] [DecidableEq I] [Fintype V]
    (w : (I → V × V) → ℝ) (E : (I ⊕ I → V) → Prop) [DecidablePred E] :
    (∑ t, if E (pairTupleLabels t) then w t else 0) =
      ∑ f, if E f then pairWeightOnLabels w f else 0 := by
  have h := pairTupleLabels_sum (fun f => if E f then pairWeightOnLabels w f else 0)
  convert h using 1
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> rfl

theorem pairWeightOnLabels_separated {I V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (w : (I → V × V) → ℝ) :
    pairWeightOnLabels (separatedPairWeight π b w) = separatedWeight π b (pairWeightOnLabels w) := by
  funext f
  have he : pairTupleLabels (fun i => (f (Sum.inl i),f (Sum.inr i))) = f := by
    funext s; cases s <;> rfl
  simp only [pairWeightOnLabels,separatedPairWeight,separatedWeight,he]

theorem separatedPairWeight_one_position {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (hc : 2 ≤ Fintype.card (I ⊕ I))
    (s : I ⊕ I) (x : V) (w : (I → V × V) → ℝ) (hw : ∀ f, 0 ≤ w f)
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ f, w f ≤ C / (Fintype.card V : ℝ) ^ (Fintype.card (I ⊕ I) - 2)) :
    (∑ t, if pairTupleLabels t s = x then w t else 0) -
        (Fintype.card (I ⊕ I) : ℝ)^2*(2*b+1)*C ≤
        (∑ t, if pairTupleLabels t s = x then separatedPairWeight π b w t else 0) ∧
      (∑ t, if pairTupleLabels t s = x then separatedPairWeight π b w t else 0) ≤
        (∑ t, if pairTupleLabels t s = x then w t else 0) := by
  have h := separatedWeight_one_position π b hc s x (pairWeightOnLabels w)
    (fun f => hw _) C hC (fun f => hupper _)
  rw [← pairWeightOnLabels_separated π b w] at h
  simpa only [← pairWeightOnLabels_incidence] using h

theorem separatedPairWeight_two_positions {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (hc : 3 ≤ Fintype.card (I ⊕ I))
    (s r : I ⊕ I) (hsr : s ≠ r) (x y : V) (hxy : ¬ PermutationClose π b x y)
    (w : (I → V × V) → ℝ) (hw : ∀ f, 0 ≤ w f) (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ f, w f ≤ C / (Fintype.card V : ℝ) ^ (Fintype.card (I ⊕ I) - 2)) :
    (∑ t, if pairTupleLabels t s = x ∧ pairTupleLabels t r = y then w t else 0) -
        (Fintype.card (I ⊕ I) : ℝ)^2*(2*b+1)*C / Fintype.card V ≤
        (∑ t, if pairTupleLabels t s = x ∧ pairTupleLabels t r = y then separatedPairWeight π b w t else 0) ∧
      (∑ t, if pairTupleLabels t s = x ∧ pairTupleLabels t r = y then separatedPairWeight π b w t else 0) ≤
        (∑ t, if pairTupleLabels t s = x ∧ pairTupleLabels t r = y then w t else 0) := by
  have h := separatedWeight_two_positions π b hc s r hsr x y hxy (pairWeightOnLabels w)
    (fun f => hw _) C hC (fun f => hupper _)
  rw [← pairWeightOnLabels_separated π b w] at h
  simpa only [← pairWeightOnLabels_incidence] using h

end Oberwolfach
