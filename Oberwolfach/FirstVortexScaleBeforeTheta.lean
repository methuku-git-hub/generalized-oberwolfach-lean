module

public import Oberwolfach.FirstVortexScaleForAssignedEdges

@[expose] public section
/-! Fix the vortex scale before θ while controlling the matching term for
every later θ at most one. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_scale_before_theta
    (cap a upper:ℝ) (hcap:0<cap) (ha:0<a) (hupper:0<upper):
    ∃ε:ℝ,0<ε ∧ ε≤upper ∧ ε≤1 ∧
      ∀θ:ℝ,θ≤1→θ*ε≤cap*a/4096 :=by
  obtain ⟨ε,hε,hupper',hε1,hbound⟩:=first_vortex_scale_for_assigned_edges cap a 1 upper hcap ha (by norm_num) hupper
  refine ⟨ε,hε,hupper',hε1,?_⟩
  intro θ hθ
  have hh:=mul_le_mul_of_nonneg_right hθ hε.le
  nlinarith only [hh,hbound]
end Oberwolfach
