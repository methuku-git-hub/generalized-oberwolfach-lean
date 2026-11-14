module

public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! Choose positive auxiliary list and deletion margins and a lower bound for
spacing; the displayed errors then hold for all sufficiently large orders. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach

theorem long_selected_list_margins (θ γ pstar:ℝ) (hθ:0<θ) (hγ:0<γ) (hp:0<pstar):
    ∃β lam ζ:ℝ,0<β ∧ β≤1 ∧ 0<lam ∧ lam≤θ ∧ 0<ζ ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*θ ∧
      (lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n:=by
  let c:=γ*pstar^2
  let β:=min (1:ℝ) (c*θ/2)
  let lam:=min θ (β/8)
  let ζ:=β/16
  have hc:0<c:=by dsimp [c];positivity
  have hβ:0<β:=lt_min (by norm_num) (by positivity)
  have hβ1:β≤1:=min_le_left _ _
  have hβc:β≤c*θ/2:=min_le_right _ _
  have hlam:0<lam:=lt_min hθ (by positivity)
  have hlamθ:lam≤θ:=min_le_left _ _
  have hlamβ:lam≤β/8:=min_le_right _ _
  have hζ:0<ζ:=by dsimp [ζ];positivity
  obtain ⟨D,hD⟩:=exists_nat_gt (1/(2*β))
  refine ⟨β,lam,ζ,hβ,hβ1,hlam,hlamθ,hζ,max D 2,?_⟩
  intro d hd hd2
  have hdR:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hD':1/(2*β)≤(d:ℝ):=le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (show D≤d by omega)))
  have hdinv:1/(8*(d:ℝ))≤β/4:=by
    apply (div_le_iff₀ (by positivity : 0<8*(d:ℝ))).2
    have hmul:1≤(d:ℝ)*(2*β):=(div_le_iff₀ (by positivity : 0<2*β)).1 hD'
    nlinarith
  obtain ⟨N₀,hN₀⟩:=eventually_three_quarters_and_constant_le_linear c (2*(2*((3*d:ℕ):ℝ)+1)) hc
  obtain ⟨N₁,hN₁⟩:=eventually_three_quarters_and_constant_le_linear (c*θ/2) 0 (by positivity)
  obtain ⟨N₂,hN₂⟩:=eventually_three_quarters_and_constant_le_linear (β/4) 0 (by positivity)
  refine ⟨max (max N₀ N₁) N₂,?_⟩
  intro n hn
  have hnR:(0:ℝ)≤n:=by positivity
  have h0:=hN₀ n (by omega)
  have h1:=hN₁ n (by omega)
  have h2:=hN₂ n (by omega)
  have hpow:(0:ℝ)≤(n:ℝ)^(3/4:ℝ):=by positivity
  have hdge:(2:ℝ)≤d:=by exact_mod_cast hd2
  have hquot:2*(n:ℝ)^(3/4:ℝ)/d≤(n:ℝ)^(3/4:ℝ):=by
    apply (div_le_iff₀ hdR).2
    nlinarith
  have hfrac:(n:ℝ)/(8*(d:ℝ))≤(β/4)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hdinv hnR
    calc
      _ = (1/(8*(d:ℝ)))*n:=by ring
      _ ≤ _:=hh
  have hlamζ:lam+2*ζ≤β/4:=by dsimp [ζ];linarith
  have hβn:=mul_le_mul_of_nonneg_right hβc hnR
  have hln:=mul_le_mul_of_nonneg_right hlamζ hnR
  dsimp only [c] at *
  refine ⟨h0,?_,?_⟩ <;> nlinarith
end Oberwolfach
