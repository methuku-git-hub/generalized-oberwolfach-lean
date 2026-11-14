module

public import Oberwolfach.OrderedSampleConcentration
public import Oberwolfach.UniformFibres

@[expose] public section

/-! Fixed-cardinality subsets are sampled uniformly, not by independent inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev FixedSubset (V : Type*) (r : ℕ) := {S : Finset V // S.card = r}

def orderedSampleRange {V : Type*} {r : ℕ} (σ : Fin r ↪ V) : FixedSubset V r :=
  ⟨Finset.univ.map σ, by simp⟩

def orderedSampleRangeFibreEquiv {V : Type*} [Fintype V] {r : ℕ}
    (S : FixedSubset V r) :
    {σ : Fin r ↪ V // orderedSampleRange σ = S} ≃ (Fin r ↪ {x : V // x ∈ S.1}) where
  toFun τ :=
    { toFun := fun i => ⟨τ.1 i, by
        have he := congrArg Subtype.val τ.2
        change Finset.univ.map τ.1 = S.1 at he
        rw [← he]
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      inj' := fun _ _ h => τ.1.injective (congrArg Subtype.val h) }
  invFun η := ⟨η.trans (Function.Embedding.subtype _), by
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact (η i).2
    · simp [orderedSampleRange, S.2]⟩
  left_inv τ := by apply Subtype.ext; ext i; rfl
  right_inv η := by ext i; rfl

theorem orderedSampleRange_uniform {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (Fin r ↪ V)] [Nonempty (FixedSubset V r)] :
    (FiniteLaw.uniform (Fin r ↪ V)).map orderedSampleRange =
      FiniteLaw.uniform (FixedSubset V r) := by
  let : DecidableEq (FixedSubset V r) := Classical.decEq _
  apply finiteLaw_uniform_map_equal_fibres _ (r.descFactorial r)
  intro S
  calc
    _ = Fintype.card (Fin r ↪ {x : V // x ∈ S.1}) := by
      apply Fintype.card_congr
      exact orderedSampleRangeFibreEquiv S
    _ = r.descFactorial r := by rw [Fintype.card_embedding_eq]; simp [S.2]

theorem fixedSubset_nonempty {V : Type*} [Fintype V] {r : ℕ}
    (hr : r ≤ Fintype.card V) : Nonempty (FixedSubset V r) := by
  obtain ⟨σ⟩ := orderedSample_nonempty hr
  exact ⟨orderedSampleRange σ⟩

def fixedSubsetMap {V : Type*} {r : ℕ} (e : Equiv.Perm V) (S : FixedSubset V r) :
    FixedSubset V r := ⟨S.1.map e.toEmbedding, by simpa using S.2⟩

theorem orderedSampleRange_trans {V : Type*} {r : ℕ} (e : Equiv.Perm V) (σ : Fin r ↪ V) :
    orderedSampleRange (σ.trans e.toEmbedding) = fixedSubsetMap e (orderedSampleRange σ) := by
  apply Subtype.ext
  exact (Finset.map_map _ _ _).symm

theorem fixedSubset_mgf
    {r : ℕ} {V : Type*} [Fintype V]
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V)
    (f : FixedSubset V r → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ S u v, |f S - f (fixedSubsetMap (Equiv.swap u v) S)| ≤ b)
    (t : ℝ) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => Real.exp (t * (f S - (FiniteLaw.uniform (FixedSubset V r)).expectation f))) ≤
      Real.exp (t ^ 2 * (r : ℝ) * b ^ 2 / 8) := by
  let := orderedSample_nonempty hr
  rw [← orderedSampleRange_uniform, finiteLaw_map_expectation, finiteLaw_map_expectation]
  apply orderedSample_mgf hr _ hb
  intro σ u v
  rw [orderedSampleRange_trans]
  exact hexchange (orderedSampleRange σ) u v

end Oberwolfach
