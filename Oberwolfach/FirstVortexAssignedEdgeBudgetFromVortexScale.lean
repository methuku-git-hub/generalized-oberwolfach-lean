module

public import Oberwolfach.FirstVortexAssignedEdgeLoadBound

@[expose] public section
/-! After the vortex scale is fixed, the assigned bad-edge endpoints fit
the local error budget. The θ term is controlled by the vortex scale, allowing θ to remain larger than the transfer cap. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_assigned_edge_local_budget_from_vortex_scale
    (cap a ε θ lam:ℝ) (d:ℕ) (hcap:0<cap) (ha:0<a) (hε:0<ε) (hε1:ε≤1)
    (hθ0:0≤θ) (hθε:θ*ε≤cap*a/4096) (hlam:lam≤cap*a/4096):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀E:ℕ,
      (E:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n→
      2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  let C:ℝ:=96*(d:ℝ)/a+1
  have hC:0<C:=by dsimp [C]; positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (512*C/(cap*ε))
  refine ⟨N,?_⟩
  intro n hn hn0 E hE
  have hnR:0<(n:ℝ):=by exact_mod_cast hn0
  have hNn:(N:ℝ)≤n:=by exact_mod_cast hn
  have hlarge:512*C<cap*ε*n:=by
    have hp:0<cap*ε:=mul_pos hcap hε
    have hh:512*C<(N:ℝ)*(cap*ε):=(div_lt_iff₀ hp).mp hN
    have hh':(cap*ε)*(N:ℝ)≤(cap*ε)*n:=mul_le_mul_of_nonneg_left hNn (by positivity)
    nlinarith only [hh,hh']
  have hθεmul:=mul_le_mul_of_nonneg_right hθε hε.le
  have hlamMul:=mul_le_mul_of_nonneg_right hlam hε.le
  have hcoeff0:8*(θ*ε^2+lam*ε)≤(cap*ε/256)*a:=by nlinarith [hθεmul,hlamMul]
  have hcoeff:8*(θ*ε^2+lam*ε)*(1/a)≤cap*ε/256:=by
    have hh:8*(θ*ε^2+lam*ε)/a≤cap*ε/256:=(div_le_iff₀ ha).2 hcoeff0
    convert hh using 1 <;> ring
  have hlinear:=mul_le_mul_of_nonneg_right hcoeff hnR.le
  have hload:=first_vortex_assigned_edge_load_bound n d E θ ε lam a hn0 ha hE
  dsimp only [C] at hlarge
  nlinarith only [hload,hlinear,hlarge]
end Oberwolfach
