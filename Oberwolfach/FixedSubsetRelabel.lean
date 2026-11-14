module

public import Oberwolfach.FixedSubsets

@[expose] public section
/-! An exact relabelling of fixed-size subsets and their uniform law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fixedSubsetRelabelEquiv {V W : Type*} {t : ℕ} (e : V ≃ W) :
    FixedSubset V t ≃ FixedSubset W t where
  toFun S := ⟨S.val.map e.toEmbedding, by simpa using S.property⟩
  invFun S := ⟨S.val.map e.symm.toEmbedding, by simpa using S.property⟩
  left_inv S := by
    apply Subtype.ext
    ext x
    simp
  right_inv S := by
    apply Subtype.ext
    ext x
    simp

theorem fixed_subset_relabel_uniform {V W : Type*} [Fintype V] [Fintype W] {t : ℕ}
    [Nonempty (FixedSubset V t)] [Nonempty (FixedSubset W t)] (e : V ≃ W) :
    (FiniteLaw.uniform (FixedSubset V t)).map (fixedSubsetRelabelEquiv e) =
      FiniteLaw.uniform (FixedSubset W t) :=
  finiteLaw_uniform_map_equiv (fixedSubsetRelabelEquiv e)
end Oberwolfach
