module

public import Oberwolfach.FirstVortexLocalChainRateBudget

@[expose] public section
/-! Choose the correction rate after the inner balance tolerance and the
vortex scale, while retaining any earlier upper bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_chain_rate_choice (cap c ε ρ:ℝ)
    (hcap:0<cap) (hc:0<c) (hε:0<ε) (hρ:0<ρ):
    ∃t:ℝ,0<t ∧ t≤cap ∧ (17+4/ρ)*t≤c*ε/2 :=by
  let A:ℝ:=17+4/ρ
  have hA:0<A:=by dsimp [A];positivity
  let t:=min (cap/2) ((c*ε)/(4*A))
  have ht:0<t:=by dsimp [t];positivity
  have htcap:t≤cap/2:=min_le_left _ _
  have htrate:t≤(c*ε)/(4*A):=min_le_right _ _
  refine ⟨t,ht,by linarith,?_⟩
  have hh:=mul_le_mul_of_nonneg_left htrate hA.le
  have hEq:A*((c*ε)/(4*A))=c*ε/4:=by field_simp
  rw [hEq] at hh
  change A*t≤c*ε/2
  have hh0:0≤c*ε:=mul_nonneg hc.le hε.le
  linarith
end Oberwolfach
