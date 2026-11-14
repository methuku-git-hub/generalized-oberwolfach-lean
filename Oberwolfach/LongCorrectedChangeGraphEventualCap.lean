module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! Absorb the two sublinear errors and the fixed spacing cost in the same
linear change cap used for the corrected parent and robust absorber. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem long_corrected_change_graph_eventual_cap
    (d:ℕ) (θ a γ ξClass δglobal Δ ζSpoke rho eta cap:ℝ)
    (hζ:ζSpoke≤cap)
    (hgap:2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<cap):
    ∃N:ℕ,∀n:ℕ,N≤n→
      ((2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ))+
        Δ*n+((1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ))≤cap*n ∧
      ζSpoke*n≤cap*n :=by
  let c:=2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta
  have hc:0<cap-c:=by dsimp [c];linarith
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 2 (2*(6*d+2:ℕ)) 1 (2/5) (cap-c)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) hc
  refine ⟨N,?_⟩
  intro n hn
  have herr:=hN n hn ((n:ℝ)^(3/5:ℝ)) (by norm_num)
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hz:=mul_le_mul_of_nonneg_right hζ hn0
  constructor
  · dsimp [c] at herr
    push_cast at *
    nlinarith only [herr]
  · exact hz
end Oberwolfach
