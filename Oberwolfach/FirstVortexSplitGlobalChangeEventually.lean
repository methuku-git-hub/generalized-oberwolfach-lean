module

public import Oberwolfach.LongSplitLoadRobustChangeBudget
public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The split-load global rim and spoke budgets follow eventually from
strict linear rate margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_split_global_change_eventually
    (d:ℕ) (ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ rho eta ζChange:ℝ)
    (hrow:2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eta)<ζChange)
    (hcol:2*(ζret+10*θ)+ηBalance≤ζChange):
    ∃N:ℕ,∀n:ℕ,N≤n→
      2*(ζret*n+(δspoke*n+(Real.sqrt δspoke*n+1)))+
        (ηBalance*n+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+
          (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)))≤ζChange*n ∧
      2*(ζret*n+10*θ*n)+ηBalance*n≤ζChange*n :=by
  let L:ℝ:=2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eta)
  let C:ℝ:=8+4*(6*d+2:ℕ)
  let gap:=ζChange-L
  have hgap:0<gap:=by dsimp [gap,L];linarith
  have hC:0≤C:=by dsimp [C];positivity
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 2 C 1 (2/5) gap
    (by norm_num) hC (by norm_num) (by norm_num) hgap
  refine ⟨N,?_⟩
  intro n hn
  have herr:=hN n hn ((n:ℝ)^(3/5:ℝ)) (by norm_num)
  have heq:2*(ζret*n+(δspoke*n+(Real.sqrt δspoke*n+1)))+
      (ηBalance*n+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δsmall*n+(κ*n+1)))+
        (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)))=
      L*n+2*(n:ℝ)^(3/5:ℝ)+C:=by dsimp [L,C];push_cast;ring
  have hcolN:=mul_le_mul_of_nonneg_right hcol (show (0:ℝ)≤n by positivity)
  constructor
  · rw [heq]
    dsimp [gap] at herr
    nlinarith
  · nlinarith
end Oberwolfach
