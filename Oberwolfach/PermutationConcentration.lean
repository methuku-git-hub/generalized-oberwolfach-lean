module

public import Oberwolfach.OrderedSampleConcentration

@[expose] public section

/-! Uniform permutations with a single transposition as the permitted exchange. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def orderedSamplePermutationEquiv (V : Type*) [Fintype V] :
    (Fin (Fintype.card V) ↪ V) ≃ Equiv.Perm V :=
  (Equiv.embeddingCongr (Fintype.equivFin V).symm (Equiv.refl V)).trans
    (Equiv.embeddingEquivOfFinite V)

theorem orderedSamplePermutationEquiv_trans {V : Type*} [Fintype V]
    (σ : Fin (Fintype.card V) ↪ V) (e : Equiv.Perm V) :
    orderedSamplePermutationEquiv V (σ.trans e.toEmbedding) =
      (orderedSamplePermutationEquiv V σ).trans e := by
  ext x
  rfl

theorem uniformPermutation_mgf
    {V : Type*} [Fintype V] (f : Equiv.Perm V → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ σ u v, |f σ - f (σ.trans (Equiv.swap u v))| ≤ b)
    (t : ℝ) :
    (FiniteLaw.uniform (Equiv.Perm V)).expectation
      (fun σ => Real.exp (t * (f σ - (FiniteLaw.uniform (Equiv.Perm V)).expectation f))) ≤
      Real.exp (t ^ 2 * (Fintype.card V : ℝ) * b ^ 2 / 8) := by
  let : Nonempty (Fin (Fintype.card V) ↪ V) := orderedSample_nonempty (le_refl _)
  let e := orderedSamplePermutationEquiv V
  rw [← finiteLaw_uniform_map_equiv e, finiteLaw_map_expectation, finiteLaw_map_expectation]
  apply orderedSample_mgf (le_refl _) _ hb
  intro σ u v
  rw [orderedSamplePermutationEquiv_trans]
  exact hexchange (e σ) u v

end Oberwolfach
