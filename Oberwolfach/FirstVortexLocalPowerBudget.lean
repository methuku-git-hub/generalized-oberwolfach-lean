module

public import Oberwolfach.FirstVortexLocalLoadPowerMargins
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
/-! The local three-quarter-power error fits the first-active budget after
the vortex scale and the positive cap have been fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_power_budget
    (ε cap:ℝ) (hε:0<ε) (hcap:0<cap):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n))
      (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),0<m→
      ((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)≤cap*(ε*n)/128 :=by
  obtain ⟨N,hN⟩:=first_vortex_local_load_power_margins ε cap cap hε hcap hcap
  refine ⟨N,?_⟩
  intro n hn U _ G D m β Q hm
  have hp:((Q.extendedVertices 1).card:ℝ)^(3/4:ℝ)≤(cap/4096)*((Q.extendedVertices 1).card:ℝ):=(hN n hn U G D m β Q hm).2
  have hs:=Q.first_inner_vertex_size_upper hε.le
  simp only [Fintype.card_fin] at hs
  have hmul:=mul_le_mul_of_nonneg_left hs (show 0≤cap/4096 by positivity)
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hpos:0≤cap*ε*n:=mul_nonneg (mul_nonneg hcap.le hε.le) hn0
  nlinarith only [hp,hmul,hpos]
end Oberwolfach
