module

public import Oberwolfach.ProtectedPartitionFamily

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem regularDegree_colourDensities {k D : ℕ} (m : Fin k → ℕ)
    (hD : 0 < D) (heven : Even D) (hsum : ∑ a, m a = D / 2) :
    (∀ a, 0 ≤ 2 * (m a : ℝ) / D) ∧
    (∑ a, 2 * (m a : ℝ) / D = 1) ∧
    (∀ a, (2 * (m a : ℝ) / D) / 2 * D = (m a : ℝ)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hhalf : 2 * (D / 2) = D := by obtain ⟨d, hd⟩ := heven; omega
  have hs : 2 * (∑ a, (m a : ℝ)) = D := by
    rw [← Nat.cast_sum]
    exact_mod_cast (show 2 * (∑ a, m a) = D by rw [hsum]; exact hhalf)
  refine ⟨fun a => by positivity, ?_, ?_⟩
  · rw [← Finset.sum_div, ← Finset.mul_sum, hs, div_self hDr.ne']
  · intro a
    field_simp

end Oberwolfach
