module

public import Oberwolfach.SuccessorSequenceWeights
public import Oberwolfach.MarkedPermutationEmbedding

@[expose] public section
/-! Transport a fixed successor-sequence weighting by a full bijection.
The weight is reindexed, not recomputed. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem successor_sequence_valid_relabel {c : ℕ} (f : W ≃ V)
    (G : SimpleGraph V) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (z : Fin c → W) :
    SuccessorSequenceValid (G.comap f) ρ z ↔ SuccessorSequenceValid G π (f ∘ z) := by
  simp only [SuccessorSequenceValid, Function.comp_apply, SimpleGraph.comap_adj]
  apply forall_congr'
  intro j
  split_ifs <;> simp [hc]

theorem successor_sequence_weights_relabel {c : ℕ} (f : W ≃ V)
    (G : SimpleGraph V) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (b : ℕ) (D τ A B : ℝ)
    (w : (Fin c → V) → ℝ)
    (hw : SuccessorSequenceWeightConditions G π b D τ A B w) :
    SuccessorSequenceWeightConditions (G.comap f) ρ b D τ A B (fun z => w (f ∘ z)) := by
  letI : DecidableEq W := fun x y => Classical.propDecidable (x = y)
  letI : DecidableEq V := fun x y => Classical.propDecidable (x = y)
  let e : (Fin c → W) ≃ (Fin c → V) := Equiv.piCongrRight (fun _ => f)
  have he (z : Fin c → W) : e z = f ∘ z := rfl
  have hcard : Fintype.card W = Fintype.card V := Fintype.card_congr f
  refine ⟨fun z => hw.nonneg (f ∘ z), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hv,hs⟩ := hw.support (f ∘ z) hz
    exact ⟨(successor_sequence_valid_relabel f G π ρ hc z).mpr hv,
      (permutationSeparated_embedding_iff f.toEmbedding ρ π hc b z).mp hs⟩
  · intro z
    simpa only [hcard] using hw.upper (f ∘ z)
  · intro z hv hs
    have hv' := (successor_sequence_valid_relabel f G π ρ hc z).mp hv
    have hs' := (permutationSeparated_embedding_iff f.toEmbedding ρ π hc b z).mpr hs
    simpa only [hcard] using hw.lower (f ∘ z) hv' hs'
  · intro j x y hxy hadj
    have hxy' : ¬ PermutationClose π b (f x) (f y) := by
      intro h
      exact hxy ((permutationClose_embedding_iff f.toEmbedding ρ π hc b x y).mp h)
    have hadj' : G.Adj (f x) (if j.val+1=c then π (f y) else f y) := by
      change G.Adj (f x) (f (if j.val+1=c then ρ y else y)) at hadj
      split_ifs at hadj ⊢ <;> simp_all [hc]
    have hh := hw.edges j (f x) (f y) hxy' hadj'
    have hsum : (∑ z : Fin c → W, if z j=x ∧ z (cycleNext j)=y then w (f ∘ z) else 0) =
        ∑ z : Fin c → V, if z j=f x ∧ z (cycleNext j)=f y then w z else 0 := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro z _
      simp only [he,Function.comp_apply,f.injective.eq_iff]
    change (1-τ ≤ ∑ z : Fin c → W, if z j=x ∧ z (cycleNext j)=y then w (f ∘ z) else 0) ∧
      (∑ z : Fin c → W, if z j=x ∧ z (cycleNext j)=y then w (f ∘ z) else 0) ≤ 1
    rw [hsum]
    exact hh
  · intro j x
    have hh := hw.positions j (f x)
    have hsum : (∑ z : Fin c → W, if z j=x then w (f ∘ z) else 0) =
        ∑ z : Fin c → V, if z j=f x then w z else 0 := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro z _
      simp only [he,Function.comp_apply,f.injective.eq_iff]
    change ((1-τ)*D ≤ ∑ z : Fin c → W, if z j=x then w (f ∘ z) else 0) ∧
      (∑ z : Fin c → W, if z j=x then w (f ∘ z) else 0) ≤ D
    rw [hsum]
    exact hh
end Oberwolfach
