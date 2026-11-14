module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-! Nested finite sets with any prescribed nonincreasing cardinalities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def finiteInitialSegment {V : Type*} [Fintype V] (k : ℕ) : Finset V :=
  Finset.univ.filter (fun x => ((Fintype.equivFin V) x).val < k)

def finiteInitialSegmentEquiv {V : Type*} [Fintype V] {k : ℕ}
    (hk : k ≤ Fintype.card V) : Fin k ≃ {x : V // x ∈ finiteInitialSegment k} where
  toFun i := ⟨(Fintype.equivFin V).symm ⟨i.val, lt_of_lt_of_le i.isLt hk⟩, by
    simp only [finiteInitialSegment, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.apply_symm_apply]
    exact i.isLt⟩
  invFun x := ⟨((Fintype.equivFin V) x.1).val, (Finset.mem_filter.mp x.2).2⟩
  left_inv i := by apply Fin.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem finiteInitialSegment_card {V : Type*} [Fintype V] {k : ℕ}
    (hk : k ≤ Fintype.card V) : (finiteInitialSegment (V := V) k).card = k := by
  have hh := Fintype.card_congr (finiteInitialSegmentEquiv (V := V) hk)
  simpa only [Fintype.card_fin, Fintype.card_coe] using hh.symm

theorem finiteInitialSegment_mono {V : Type*} [Fintype V] {j k : ℕ} (hjk : j ≤ k) :
    finiteInitialSegment (V := V) j ⊆ finiteInitialSegment k := by
  intro x hx
  have hx' := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hx' hjk⟩

theorem finiteInitialSegment_full {V : Type*} [Fintype V] :
    finiteInitialSegment (V := V) (Fintype.card V) = Finset.univ := by
  ext x
  simp only [finiteInitialSegment, Finset.mem_filter, Finset.mem_univ, true_and]
  exact iff_true_intro ((Fintype.equivFin V) x).isLt

theorem nested_finsets_of_sizes {V : Type*} [Fintype V] (n : ℕ → ℕ)
    (hzero : n 0 = Fintype.card V) (hmono : Antitone n) :
    ∃ B : ℕ → Finset V, B 0 = Finset.univ ∧
      (∀ i, (B i).card = n i) ∧ ∀ i, B (i + 1) ⊆ B i := by
  refine ⟨fun i => finiteInitialSegment (n i), ?_, ?_, ?_⟩
  · dsimp only
    rw [hzero, finiteInitialSegment_full]
  · intro i
    apply finiteInitialSegment_card
    rw [← hzero]
    exact hmono (Nat.zero_le _)
  · intro i
    exact finiteInitialSegment_mono (hmono (by omega))

end Oberwolfach
