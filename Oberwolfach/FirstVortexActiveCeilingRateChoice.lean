module

public import Oberwolfach.FirstVortexActiveCeilingEventually

@[expose] public section
/-! The active ceiling has a strict margin with positive rates below any
previously fixed cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_active_ceiling_rate_choice
    (ρ ε cap upper:ℝ) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap) (hupper:0<upper):
    ∃θ lamAssign:ℝ,0<θ ∧ 0<lamAssign ∧ θ≤upper ∧ lamAssign≤upper ∧
      8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128 :=by
  let c:ℝ:=(ρ/4)/40000
  have hc:0<c:=by dsimp [c];positivity
  let t:ℝ:=min (upper/2) (cap*c/(8192*(ε+1)))
  have ht:0<t:=by dsimp [t];positivity
  have htup:t≤upper/2:=min_le_left _ _
  have htsmall:t≤cap*c/(8192*(ε+1)):=min_le_right _ _
  have heps:0<ε+1:=by linarith
  have hprod:t*(ε+1)≤cap*c/8192:=by
    have hh:=(le_div_iff₀ (show 0<8192*(ε+1) by positivity)).mp htsmall
    nlinarith
  have hmul:=mul_le_mul_of_nonneg_left hprod (show 0≤8*ε/c by positivity)
  have heq1:(8*ε/c)*(t*(ε+1))=8*(t*ε^2+t*ε)/c:=by ring
  have heq2:(8*ε/c)*(cap*c/8192)=cap*ε/1024:=by field_simp;ring
  rw [heq1,heq2] at hmul
  refine ⟨t,t,ht,ht,by linarith,by linarith,?_⟩
  change 8*(t*ε^2+t*ε)/c<cap*ε/128
  have hp:0<cap*ε:=mul_pos hcap hε
  linarith
end Oberwolfach
