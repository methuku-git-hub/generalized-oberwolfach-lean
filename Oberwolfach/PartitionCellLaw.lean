module

public import Oberwolfach.FixedPartitions
public import Oberwolfach.FixedSubsets
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-! A specified cell of a uniform prescribed-size partition is a uniform
subset of the prescribed size, with no change of sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fixedPartitionCell {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P : FixedPartition V k d) (a : Fin k) : FixedSubset V (d a) :=
  ⟨Finset.univ.filter (fun x => P.1 x = a), by
    simpa only [Fintype.card_subtype] using P.2 a⟩

theorem fixedPartitionCell_map {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (e : Equiv.Perm V) (P : FixedPartition V k d) (a : Fin k) :
    fixedPartitionCell (fixedPartitionMap e P) a = fixedSubsetMap e (fixedPartitionCell P a) := by
  apply Subtype.ext
  ext x
  simp only [fixedPartitionCell, fixedPartitionMap, fixedSubsetMap, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨e.symm x, h, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [e.symm_apply_apply] using hy

def fixedPartitionPermEquiv {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (e : Equiv.Perm V) : FixedPartition V k d ≃ FixedPartition V k d where
  toFun := fixedPartitionMap e
  invFun := fixedPartitionMap e.symm
  left_inv P := by apply Subtype.ext; funext x; simp [fixedPartitionMap]
  right_inv P := by apply Subtype.ext; funext x; simp [fixedPartitionMap]

theorem fixedSubsetMap_injective {V : Type*} {r : ℕ} (e : Equiv.Perm V) :
    Function.Injective (fixedSubsetMap (r := r) e) := by
  intro S T h
  apply Subtype.ext
  exact Finset.map_injective e.toEmbedding (congrArg Subtype.val h)

theorem fixedSubset_permutation {V : Type*} [Fintype V] {r : ℕ}
    (S T : FixedSubset V r) : ∃ e : Equiv.Perm V, fixedSubsetMap e S = T := by
  let f : {x // x ∈ S.1} ≃ {x // x ∈ T.1} := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_coe] using S.2.trans T.2.symm)
  refine ⟨f.extendSubtype, ?_⟩
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact f.extendSubtype_mem x hx
  · simpa only [fixedSubsetMap, Finset.card_map, S.2, T.2] using (le_refl r)

theorem fixedPartition_cell_uniform {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)] (a : Fin k)
    [Nonempty (FixedSubset V (d a))] :
    (FiniteLaw.uniform (FixedPartition V k d)).map (fun P => fixedPartitionCell P a) =
      FiniteLaw.uniform (FixedSubset V (d a)) := by
  apply finiteLaw_uniform_map_transitive
  intro S T
  obtain ⟨e, he⟩ := fixedSubset_permutation S T
  refine ⟨fixedPartitionPermEquiv e, ?_⟩
  intro P
  change fixedPartitionCell (fixedPartitionMap e P) a = T ↔ fixedPartitionCell P a = S
  rw [fixedPartitionCell_map, ← he]
  exact (fixedSubsetMap_injective e).eq_iff

end Oberwolfach
