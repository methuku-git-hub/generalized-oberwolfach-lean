module

public import Oberwolfach.PermutationConcentration
public import Oberwolfach.FixedPartitions

@[expose] public section

/-! Exchanging the cells of two vertices in a uniform fixed-size partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedPartition_mgf
    {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    [Nonempty (FixedPartition V k d)]
    (f : FixedPartition V k d → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ P u v, |f P - f (fixedPartitionMap (Equiv.swap u v) P)| ≤ b)
    (t : ℝ) :
    (FiniteLaw.uniform (FixedPartition V k d)).expectation
      (fun P => Real.exp (t * (f P - (FiniteLaw.uniform (FixedPartition V k d)).expectation f))) ≤
      Real.exp (t ^ 2 * (Fintype.card V : ℝ) * b ^ 2 / 8) := by
  let P := Classical.choice (inferInstance : Nonempty (FixedPartition V k d))
  rw [← fixedPartition_uniform P, finiteLaw_map_expectation, finiteLaw_map_expectation]
  apply uniformPermutation_mgf _ hb
  intro σ u v
  rw [← fixedPartitionMap_trans]
  exact hexchange (fixedPartitionMap σ P) u v

end Oberwolfach
