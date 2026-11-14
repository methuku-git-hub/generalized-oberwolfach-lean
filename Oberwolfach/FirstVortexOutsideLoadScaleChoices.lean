module

public import Oberwolfach.FirstVortexAmbientBoundaryRelative

@[expose] public section
/-! Quantitative allocation for the completion load at the first inner scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_outside_load_scale_choices
    (ε β c:ℝ) (hε:0<ε) (hβ:0<β) (hc:0<c):
    ∃κ θ cap:ℝ, 0<κ ∧ 0<θ ∧ 0<cap ∧
      10*θ≤κ*(β/4) ∧ κ≤c*ε/128 ∧ cap≤c*ε/128 ∧
      ∀(n I boundary a γ loss:ℝ), 0≤n→ε*n/2≤I→
        128/(c*ε)≤n→boundary≤c*ε*n/32→
        a≤cap→γ≤cap→loss≤c*ε*n/32→
        2*((boundary+2*(max a γ*n))+loss+(κ*n+1))≤c*I :=by
  let κ:=c*ε/128
  let θ:=κ*β/80
  let cap:=c*ε/128
  have hk:0<κ:=by dsimp [κ]; positivity
  have ht:0<θ:=by dsimp [θ]; positivity
  have hcap:0<cap:=by dsimp [cap]; positivity
  refine ⟨κ,θ,cap,hk,ht,hcap,?_,le_rfl,le_rfl,?_⟩
  · dsimp [θ]; have : 0≤κ*β:=mul_nonneg hk.le hβ.le; nlinarith
  · intro n I boundary a γ loss hn hI hnlarge hboundary ha hg hloss
    have hmax:max a γ≤cap:=max_le ha hg
    have hm:=mul_le_mul_of_nonneg_right hmax hn
    have hprod:0<c*ε:=mul_pos hc hε
    have hone:1≤(c*ε/128)*n:=by
      have hh:128≤n*(c*ε):=(div_le_iff₀ hprod).mp hnlarge
      nlinarith
    have hIc:=mul_le_mul_of_nonneg_left hI hc.le
    dsimp [κ,cap] at *
    nlinarith
end Oberwolfach
