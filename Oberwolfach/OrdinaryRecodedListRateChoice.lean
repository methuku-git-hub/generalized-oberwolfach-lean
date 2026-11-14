module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget
public import Oberwolfach.LongReservedContinuationAllMargins

@[expose] public section
/-! If the free-edge density has a fixed positive lower bound before d is
chosen, the list margins can be selected and the spacing taken large enough. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_recoded_list_rate_choice
    (γ pstar θ:ℝ) (hγ:0<γ) (hp:0<pstar) (hθ:0<θ):
    ∃β lam ζ:ℝ,0<β ∧ β≤1 ∧ 0<lam ∧ 0<ζ ∧
    ∃dMin:ℕ,2≤dMin ∧ ∀d:ℕ,dMin≤d→
    ∃N:ℕ,∀n:ℕ,N≤n→
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2)*n*(θ/2) ∧
      (lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n :=by
  let β:ℝ:=min 1 (γ*pstar^2*θ/8)
  let lam:ℝ:=β/8
  let ζ:ℝ:=β/16
  have hcoef:0<γ*pstar^2:=by positivity
  have hβ:0<β:=by dsimp [β];positivity
  have hβ1:β≤1:=min_le_left _ _
  have hβcap:β≤γ*pstar^2*θ/8:=min_le_right _ _
  have hlam:0<lam:=by dsimp [lam];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  obtain ⟨M,hM⟩:=exists_nat_gt (4/β)
  let dMin:=max M 2
  refine ⟨β,lam,ζ,hβ,hβ1,hlam,hζ,dMin,le_max_right _ _,?_⟩
  intro d hd
  have hd2:2≤d:=by dsimp [dMin] at hd;omega
  have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hMle:(M:ℝ)≤d:=by exact_mod_cast (show M≤d by dsimp [dMin] at hd;omega)
  have hdLarge:4/β≤(d:ℝ):=hM.le.trans hMle
  have hinv:1/(d:ℝ)≤β/4:=by
    have hh:4≤(d:ℝ)*β:=(div_le_iff₀ hβ).mp hdLarge
    apply (div_le_iff₀ hdR).2
    nlinarith
  have hd1:1≤(d:ℝ):=by exact_mod_cast (show 1≤d by omega)
  let η:ℝ:=min (β/8) (γ*pstar^2/4)
  have hη:0<η:=by dsimp [η];positivity
  have hηβ:η≤β/8:=min_le_left _ _
  have hηγ:η≤γ*pstar^2/4:=min_le_right _ _
  obtain ⟨Npow,hpow⟩:=eventually_sublinear_le_linear (p:=(3/4:ℝ)) (ε:=η) (by norm_num) hη
  obtain ⟨Nc,hconst⟩:=ordinary_constant_eventually_below_linear_rate (γ*pstar^2/4)
    (2*(2*((3*d:ℕ):ℝ)+1)) (by positivity)
  refine ⟨max Npow Nc,?_⟩
  intro n hn
  have hn0:0≤(n:ℝ):=by positivity
  have hpw: (n:ℝ)^(3/4:ℝ)≤η*n:=hpow n (by omega)
  have hc:2*(2*((3*d:ℕ):ℝ)+1)≤(γ*pstar^2/4)*n:=hconst n (by omega)
  have herrβ:(n:ℝ)^(3/4:ℝ)≤(β/8)*n:=hpw.trans (mul_le_mul_of_nonneg_right hηβ hn0)
  have herrγ:(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2/4)*n:=hpw.trans (mul_le_mul_of_nonneg_right hηγ hn0)
  have hnonneg:0≤(n:ℝ)^(3/4:ℝ):=by positivity
  have hdivn:(n:ℝ)/(d:ℝ)≤(β/4)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hinv hn0
    have heq:(1/(d:ℝ))*(n:ℝ)=(n:ℝ)/(d:ℝ):=by ring
    rw [heq] at hh
    exact hh
  have hdive:2*(n:ℝ)^(3/4:ℝ)/(d:ℝ)≤(β/4)*n:=by
    have h1:2*(n:ℝ)^(3/4:ℝ)/(d:ℝ)≤2*(n:ℝ)^(3/4:ℝ):=by
      apply (div_le_iff₀ hdR).2
      nlinarith
    linarith
  refine ⟨?_,?_,?_⟩
  · linarith
  · have hh:=mul_le_mul_of_nonneg_right hβcap hn0
    nlinarith
  · dsimp [lam,ζ]
    have heq:((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)=(n:ℝ)/(d:ℝ)+2*(n:ℝ)^(3/4:ℝ)/(d:ℝ):=by ring
    rw [heq]
    linarith
end Oberwolfach
