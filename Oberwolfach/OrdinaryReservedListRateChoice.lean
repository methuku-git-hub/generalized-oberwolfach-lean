module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget
public import Oberwolfach.LongReservedContinuationAllMargins

@[expose] public section
/-! The selected reserved-list rate depends on the fixed reserve and selected
edge floors, so it is chosen before θ, spacing and the sampled host. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_list_rate_choice
    (γ pstar smin:ℝ) (hγ:0<γ) (hp:0<pstar) (hs:0<smin):
    ∃β lam ζ:ℝ,0<β ∧ β≤1 ∧ 0<lam ∧ 0<ζ ∧
      (lam+2*ζ)≤β ∧
    ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin :=by
  let β:ℝ:=min 1 (γ*pstar^2*smin/4)
  let lam:ℝ:=β/4
  let ζ:ℝ:=β/8
  have hcoef:0<γ*pstar^2:=by positivity
  have hβ:0<β:=by dsimp [β];positivity
  have hβ1:β≤1:=min_le_left _ _
  have hβcap:β≤γ*pstar^2*smin/4:=min_le_right _ _
  have hlam:0<lam:=by dsimp [lam];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  refine ⟨β,lam,ζ,hβ,hβ1,hlam,hζ,?_,?_⟩
  · dsimp [lam,ζ];linarith
  · intro d
    let η:ℝ:=min (β/4) (γ*pstar^2/4)
    have hη:0<η:=by dsimp [η];positivity
    have hηβ:η≤β/4:=min_le_left _ _
    have hηγ:η≤γ*pstar^2/4:=min_le_right _ _
    obtain ⟨Npow,hpow⟩:=eventually_sublinear_le_linear (p:=(3/4:ℝ)) (ε:=η) (by norm_num) hη
    obtain ⟨Nc,hconst⟩:=ordinary_constant_eventually_below_linear_rate (γ*pstar^2/4)
      (2*(2*((3*d:ℕ):ℝ)+1)) (by positivity)
    refine ⟨max Npow Nc,?_⟩
    intro n hn
    have hn0:(0:ℝ)≤n:=by positivity
    have hpw:(n:ℝ)^(3/4:ℝ)≤η*n:=hpow n (by omega)
    have hc:2*(2*((3*d:ℕ):ℝ)+1)≤(γ*pstar^2/4)*n:=hconst n (by omega)
    have herrβ:(n:ℝ)^(3/4:ℝ)≤(β/4)*n:=hpw.trans (mul_le_mul_of_nonneg_right hηβ hn0)
    have herrγ:(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2/4)*n:=hpw.trans (mul_le_mul_of_nonneg_right hηγ hn0)
    have hbudget:=mul_le_mul_of_nonneg_right hβcap hn0
    constructor
    · linarith
    · nlinarith
end Oberwolfach
