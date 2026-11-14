module

public import Oberwolfach.FirstVortexSplitGlobalChangeEventually

@[expose] public section
/-! Keep the global matching error and the local outside-change rate
separate in the global correction budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_split_global_change_separate_eta_eventually
    (d:ℕ) (ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ rho etaGlobal etaLocal ε ζChange:ℝ)
    (hrho:0<rho) (hη:0≤etaGlobal)
    (hrow:2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+
        (etaLocal+(ε*etaGlobal+etaLocal)/rho))<ζChange)
    (hcol:2*(ζret+10*θ)+ηBalance≤ζChange):
    ∃N:ℕ,∀n:ℕ,N≤n→∀I:ℝ,0≤I→I≤ε*n→
      2*(ζret*n+(δspoke*n+(Real.sqrt δspoke*n+1)))+
        (ηBalance*n+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+
          (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+
          (etaLocal*n+(I*etaGlobal+etaLocal*n)/rho+1)))≤ζChange*n ∧
      2*(ζret*n+10*θ*n)+ηBalance*n≤ζChange*n :=by
  let eff:ℝ:=(etaLocal+(ε*etaGlobal+etaLocal)/rho)/(1+2/rho)
  have hden:0<1+2/rho:=by positivity
  have heff:(1+2/rho)*eff=etaLocal+(ε*etaGlobal+etaLocal)/rho:=by dsimp [eff];field_simp
  have hrow':2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eff)<ζChange:=by
    rw [heff];exact hrow
  obtain ⟨N,hN⟩:=first_vortex_split_global_change_eventually d ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ rho eff ζChange hrow' hcol
  refine ⟨N,?_⟩
  intro n hn I hI hIn
  have hmul:=mul_le_mul_of_nonneg_right hIn hη
  have hquot:(I*etaGlobal+etaLocal*n)/rho≤(ε*etaGlobal+etaLocal)*(n:ℝ)/rho:=by
    apply div_le_div_of_nonneg_right _ hrho.le
    nlinarith
  have hcombine:(etaLocal+(ε*etaGlobal+etaLocal)/rho)*(n:ℝ)=
      etaLocal*n+(ε*etaGlobal+etaLocal)*(n:ℝ)/rho:=by ring
  obtain ⟨h₁,h₂⟩:=hN n hn
  rw [heff,hcombine] at h₁
  exact ⟨by linarith,h₂⟩
end Oberwolfach
