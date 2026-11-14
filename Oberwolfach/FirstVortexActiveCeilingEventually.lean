module

public import Oberwolfach.FirstVortexPrescribedActiveEventually

@[expose] public section
/-! The ceiling in the first-active spoke budget is absorbed once its
quadratic coefficient is strictly below the available linear margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_active_ceiling_eventually
    (d:ℕ) (ρ ε cap θ lamAssign:ℝ) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap)
    (hcoeff:8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128):
    ∃N:ℕ,∀n:ℕ,N≤n→∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
      2*(⌈4*(E:ℝ)/(((ρ/4)/40000)*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  let c:ℝ:=(ρ/4)/40000
  let A:ℝ:=θ*ε^2+lamAssign*ε
  let gap:ℝ:=cap*ε/128-8*A/c
  have hc:0<c:=by dsimp [c];positivity
  have hgap:0<gap:=by dsimp [gap,A,c];linarith
  let C:ℝ:=192*d/c+2
  obtain ⟨N₀,hN₀⟩:=exists_nat_gt (C/gap)
  let N:=max (N₀+1) 1
  refine ⟨N,?_⟩
  intro n hn E hE
  have hnpos:0<(n:ℝ):=by
    have hn':0<n:=by dsimp [N] at hn;omega
    exact_mod_cast hn'
  have hNlt:(N₀:ℝ)<n:=by
    have hh:N₀<n:=by dsimp [N] at hn;omega
    exact_mod_cast hh
  have hgapN:C<gap*n:=by
    have hh:C/gap<(n:ℝ):=lt_trans hN₀ hNlt
    have hh':C<(n:ℝ)*gap:=(div_lt_iff₀ hgap).mp hh
    nlinarith
  have hden:0<c*n:=mul_pos hc hnpos
  have hx:0≤4*(E:ℝ)/(c*n):=by positivity
  have hquot:4*(E:ℝ)/(c*n)≤(4*A/c)*n+96*d/c:=by
    have hh:4*(E:ℝ)/(c*n)≤4*(A*(n:ℝ)^2+24*d*n)/(c*n):=
      div_le_div_of_nonneg_right (by change (E:ℝ)≤A*(n:ℝ)^2+24*d*n at hE;linarith) hden.le
    have heq:4*(A*(n:ℝ)^2+24*d*n)/(c*n)=(4*A/c)*n+96*d/c:=by
      field_simp
      ring
    exact hh.trans_eq heq
  have hceil:=Nat.ceil_lt_add_one hx
  have hresult:2*(⌈4*(E:ℝ)/(c*n)⌉₊:ℕ)≤cap*(ε*n)/128:=by
    dsimp [gap,C] at hgapN
    have heq1:(cap*ε/128-8*A/c)*n=cap*(ε*n)/128-2*((4*A/c)*n):=by ring
    have heq2:192*(d:ℝ)/c+2=2*(96*(d:ℝ)/c)+2:=by ring
    rw [heq1,heq2] at hgapN
    linarith only [hgapN,hquot,hceil]
  simpa only [c] using hresult
end Oberwolfach
