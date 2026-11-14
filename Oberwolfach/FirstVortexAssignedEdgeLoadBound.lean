module

public import Oberwolfach.OrdinaryAssignedCapacityCeiling

@[expose] public section
/-! The first-vortex bad-edge assignment has a local load controlled by
the sampling parameters and an additive spacing term. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_assigned_edge_load_bound
    (n d E:ℕ) (θ ε lam a:ℝ) (hn:0<n) (ha:0<a)
    (hE:(E:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n):
    ((⌈4*(E:ℝ)/(a*n)⌉₊:ℕ):ℝ)≤
      4*(θ*ε^2+lam*ε)*(1/a)*n+(96*d/a+1) :=by
  have hn':0<(n:ℝ):=by exact_mod_cast hn
  have hh:=ordinary_assigned_ceiling_bound (n:ℝ) θ 1 ε lam a (24*(d:ℝ)) (E:ℝ)
    hn' ha (Nat.cast_nonneg E) (by nlinarith only [hE])
  convert hh using 1 <;> ring
end Oberwolfach
