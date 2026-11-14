module

public import Oberwolfach.VortexFirstPairProtectedSize

@[expose] public section
/-! The actual vortex may use a later, smaller contraction than the early
reserved-placement scale, while keeping both first-level size bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_below_placement_scale
    {n q D mv:ℕ} {β ε εearly:ℝ} (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (hε:0≤ε) (hscale:ε≤εearly) (hq:q≤n):
    ((Q.extendedVertices 1).card:ℝ)≤εearly*n ∧
    ((Q.extendedIndices 1).card:ℝ)≤εearly*n :=by
  obtain ⟨hV,hU⟩:=vortex_first_pair_protected_size Q hε εearly hscale
  have hscale0:0≤εearly:=hε.trans hscale
  have hqn:(q:ℝ)≤n:=by exact_mod_cast hq
  constructor
  · simpa using hV
  · have hU':((Q.extendedIndices 1).card:ℝ)≤εearly*q:=by simpa using hU
    have hh:=mul_le_mul_of_nonneg_left hqn hscale0
    exact hU'.trans hh
end Oberwolfach
