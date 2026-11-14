module

public import Oberwolfach.FirstVortexScaleBeforeTheta
public import Oberwolfach.FirstVortexAssignedEdgeBudgetFromVortexScale
public import Oberwolfach.LongPrescribedSpacingSmall

@[expose] public section
/-! Choose the vortex scale, θ, spacing and matching rate in that order so that
both the prescribed vertices and assigned matching endpoints fit the same
first-active tolerance. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_local_budget_hierarchy
    (cap a upper:ℝ) (hcap:0<cap) (ha:0<a) (hupper:0<upper):
    ∃ε:ℝ,0<ε ∧ ε≤upper ∧ ε≤1/4 ∧
    ∀θ:ℝ,0<θ→θ≤1→∀dmin:ℕ,
    ∃d:ℕ,dmin≤d ∧ 3≤d ∧ 1/(d:ℝ)≤θ/1024 ∧ ∀lam:ℝ,0≤lam→lam≤1→lam≤cap*a/4096→∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(a' γ:ℝ),
      max a' γ≤1/(10*(d:ℝ))→
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a' γ*n≤cap*(ε*n)/128 ∧
      ∀E:ℕ,(E:ℝ)≤(θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n→
        2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  obtain ⟨ε,hε,hεupper,hεone,hθε⟩:=first_vortex_scale_before_theta cap a (min upper (1/4)) hcap ha (by positivity)
  have hεupper':ε≤upper:=hεupper.trans (min_le_left _ _)
  have hεquarter:ε≤1/4:=hεupper.trans (min_le_right _ _)
  refine ⟨ε,hε,hεupper',hεquarter,?_⟩
  intro θ hθ hθ1 dmin
  have hθε':θ*ε≤cap*a/4096:=hθε θ hθ1
  obtain ⟨M,hM⟩:=exists_nat_gt (max (1280/(cap*ε)) (1024/θ))
  let d:=max dmin (max 3 M)
  have hdmin:dmin≤d:=le_max_left _ _
  have hd:3≤d:=(le_max_left 3 M).trans (le_max_right dmin _)
  have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hMR:(M:ℝ)≤d:=by exact_mod_cast ((le_max_right 3 M).trans (le_max_right dmin _))
  have hlarge:1280<((d:ℝ)*(cap*ε)):=by
    have hM':1280<(M:ℝ)*(cap*ε):=(div_lt_iff₀ (by positivity:0<cap*ε)).mp ((le_max_left (1280/(cap*ε)) (1024/θ)).trans_lt hM)
    have hh:=mul_le_mul_of_nonneg_right hMR (mul_nonneg hcap.le hε.le)
    nlinarith only [hM',hh]
  have hspacing:1/(d:ℝ)≤(cap*ε/128)/10:=by
    apply (div_le_iff₀ hdR).2
    nlinarith only [hlarge]
  have hθlarge:1024<(d:ℝ)*θ:=by
    have hM':1024<(M:ℝ)*θ:=(div_lt_iff₀ hθ).mp ((le_max_right (1280/(cap*ε)) (1024/θ)).trans_lt hM)
    have hh:=mul_le_mul_of_nonneg_right hMR hθ.le
    nlinarith only [hM',hh]
  have hθspacing:1/(d:ℝ)≤θ/1024:=by
    apply (div_le_iff₀ hdR).2
    nlinarith only [hθlarge]
  obtain ⟨Npres,hNpres⟩:=long_prescribed_spacing_eventually_small d (cap*ε/128) (by omega) (by positivity) hspacing
  refine ⟨d,hdmin,hd,hθspacing,?_⟩
  intro lam hlam hlam1 hlamcap
  obtain ⟨Nedge,hNedge⟩:=first_vortex_assigned_edge_local_budget_from_vortex_scale cap a ε θ lam d hcap ha hε (by linarith) hθ.le hθε' hlamcap
  refine ⟨max Npres Nedge,?_⟩
  intro n hn hn0 a' γ hdefect
  constructor
  · have hh:=hNpres n (by omega) a' γ hdefect
    nlinarith only [hh]
  · intro E hE
    exact hNedge n (by omega) hn0 E hE
end Oberwolfach
