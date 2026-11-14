module

public import Oberwolfach.FirstVortexSplitGlobalChangeEventually

@[expose] public section
/-! A common small upper bound suffices for all rates in the split-load
global transfer, independently of the larger embedding-host error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_split_change_rate_choice (cap rho:ℝ) (hcap:0<cap) (hrho:0<rho):
    ∃t:ℝ,0<t ∧ ∀ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ eta:ℝ,
      ζret≤t→δspoke≤t→Real.sqrt δspoke≤t→ηBalance≤t→θ≤t→a≤t→γ≤t→
      ξPart≤t→δsmall≤t→κ≤t→Δ≤t→eta≤t→
      2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
        2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eta)<cap ∧
      2*(ζret+10*θ)+ηBalance≤cap :=by
  let A:ℝ:=46+4/rho
  have hA:0<A:=by dsimp [A];positivity
  let t:=cap/(2*A)
  have ht:0<t:=by dsimp [t];positivity
  have hAt:A*t=cap/2:=by dsimp [t];field_simp
  refine ⟨t,ht,?_⟩
  intro ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ eta hζ hδ hsqrt hbal hθ ha hγ hξ hsmall hκ hΔ heta
  have hmax:max a (4*γ)≤4*t:=max_le (by linarith) (by linarith)
  have hcoef:0≤1+2/rho:=by positivity
  have hetabound:=mul_le_mul_of_nonneg_left heta hcoef
  have hsmallRate:(45+4/rho)*t<cap:=by
    have hdiff:0<(1:ℝ)*t:=by positivity
    have heq:(45+4/rho)*t=A*t-t:=by dsimp [A];ring
    rw [heq,hAt]
    linarith
  have hrow:2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eta)≤(45+4/rho)*t:=by
    have heq:(45+4/rho)*t=43*t+2*((1+2/rho)*t):=by ring
    rw [heq]
    linarith
  have hcol:2*(ζret+10*θ)+ηBalance≤23*t:=by linarith
  have h23:23*t<cap:=by
    have hfour:0≤(4/rho)*t:=by positivity
    have heq:(45+4/rho)*t=45*t+(4/rho)*t:=by ring
    rw [heq] at hsmallRate
    linarith
  exact ⟨lt_of_le_of_lt hrow hsmallRate,(le_of_lt (lt_of_le_of_lt hcol h23))⟩
end Oberwolfach
