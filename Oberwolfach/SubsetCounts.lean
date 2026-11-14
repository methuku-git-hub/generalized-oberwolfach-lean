module

public import Oberwolfach.SubsetComplement

@[expose] public section

/-! Exact inclusion probabilities for the uniform fixed-cardinality subset law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_uniform_probability
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Ω → Prop) :
    (FiniteLaw.uniform Ω).probability A = (Fintype.card {x // A x} : ℝ) / Fintype.card Ω := by
  simp [FiniteLaw.probability, FiniteLaw.uniform, Fintype.card_subtype, ← Finset.sum_filter,
    div_eq_mul_inv]

def fixedSubsetContainingEquiv {V : Type*} [Fintype V] {r : ℕ} (T : Finset V) :
    {S : FixedSubset V r // T ⊆ S.1} ≃
      {S : Finset V // S ∈ ((Finset.univ : Finset V).powersetCard r).filter (T ⊆ ·)} where
  toFun S := ⟨S.1.1, by simp [S.1.2, S.2]⟩
  invFun S := ⟨⟨S.1, (Finset.mem_powersetCard.mp (Finset.mem_filter.mp S.2).1).2⟩,
    (Finset.mem_filter.mp S.2).2⟩
  left_inv S := rfl
  right_inv S := rfl

theorem fixedSubset_containing_card {V : Type*} [Fintype V] {r : ℕ}
    (T : Finset V) (hT : T.card ≤ r) :
    Fintype.card {S : FixedSubset V r // T ⊆ S.1} =
      (Fintype.card V - T.card).choose (r - T.card) := by
  calc
    _ = Fintype.card {S : Finset V //
        S ∈ ((Finset.univ : Finset V).powersetCard r).filter (T ⊆ ·)} :=
      Fintype.card_congr (fixedSubsetContainingEquiv T)
    _ = (((Finset.univ : Finset V).powersetCard r).filter (T ⊆ ·)).card := Fintype.card_coe _
    _ = _ := by rw [Finset.card_filter_powersetCard_subset T Finset.univ r (Finset.subset_univ _) hT]; simp

theorem fixedSubset_inclusion_probability {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (T : Finset V) (hT : T.card ≤ r) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => T ⊆ S.1) =
      ((Fintype.card V - T.card).choose (r - T.card) : ℝ) / (Fintype.card V).choose r := by
  rw [finiteLaw_uniform_probability]
  congr 1
  · apply congrArg (fun k : ℕ => (k : ℝ))
    simpa only [← Nat.card_eq_fintype_card] using fixedSubset_containing_card T hT
  · exact_mod_cast Fintype.card_finset_len (α := V) r

end Oberwolfach
