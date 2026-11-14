module

public import Oberwolfach.FirstVortexAssignedEdgeLoadBound

@[expose] public section
/-! The first-vortex scale can be chosen after the positive packing and
transfer constants so that the quadratic matching-edge term is negligible. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_scale_for_assigned_edges
    (cap a θ upper:ℝ) (hcap:0<cap) (ha:0<a) (hθ:0<θ) (hupper:0<upper):
    ∃ε:ℝ,0<ε ∧ ε≤upper ∧ ε≤1 ∧ θ*ε≤cap*a/4096 :=by
  let ε:ℝ:=min upper (min 1 (cap*a/(4096*θ)))
  have he:0<ε:=by dsimp [ε];positivity
  have heupper:ε≤upper:=min_le_left _ _
  have heone:ε≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have hecap:ε≤cap*a/(4096*θ):=(min_le_right _ _).trans (min_le_right _ _)
  have hh:ε*(4096*θ)≤cap*a:=(le_div_iff₀ (by positivity:0<4096*θ)).mp hecap
  refine ⟨ε,he,heupper,heone,?_⟩
  nlinarith
end Oberwolfach
