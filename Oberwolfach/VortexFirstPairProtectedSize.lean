module

public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
/-! The first vortex pair meets the protected-correction size bounds when
the vortex density is chosen below the correction scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem vortex_first_pair_protected_size
    {V U:Type} [Fintype V] [Fintype U] {P:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε m)
    (hε:0≤ε) (h:ℝ) (hεh:ε≤h):
    ((Q.extendedVertices 1).card:ℝ)≤h*Fintype.card V ∧
    ((Q.extendedIndices 1).card:ℝ)≤h*Fintype.card U:=by
  have hV:=Q.first_inner_vertex_size_upper hε
  have hI:((Q.extendedIndices 1).card:ℝ)≤ε*Fintype.card U:=by
    rw [Q.extendedIndices_eq (by have hh:=Q.length_pos;omega),Q.index_sizes,floorOrbit_succ]
    simpa only [floorOrbit_zero] using (Nat.floor_le (show 0≤ε*Fintype.card U by positivity))
  exact ⟨hV.trans (mul_le_mul_of_nonneg_right hεh (Nat.cast_nonneg _)),
    hI.trans (mul_le_mul_of_nonneg_right hεh (Nat.cast_nonneg _))⟩
end Oberwolfach
