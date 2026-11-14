module

public import Mathlib.Tactic

@[expose] public section

/-! Choose the balancing tolerances before the bounded forbidden-set size.
The resulting inequalities are the degree, size and count margins used
by common-neighbourhood balancing. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

 theorem balanced_class_tolerances (m:ℕ) (q β η K:ℝ)
    (hq:0<q) (hβ:0<β) (hη:0<η) (hK:0≤K):
    ∃ ε δ:ℝ,0<ε∧0<δ∧ε+δ≤q/2∧ε+K*δ≤η∧(m+1)*δ≤β/2∧
      ∀ f:ℝ,0≤f→∃ N:ℕ,1≤N∧∀ n:ℕ,N≤n→
        4*(m+1)*ε*n+2*(m+1)*f+(m+1)≤δ*n:=by
  let c:ℝ:=m+1
  have hc:0<c:=by dsimp [c];positivity
  let δ:ℝ:=min (q/4) (min (η/(2*(K+1))) (β/(2*c)))
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδq:δ≤q/4:=min_le_left _ _
  have hδη:δ≤η/(2*(K+1)):=(min_le_right _ _).trans (min_le_left _ _)
  have hδβ:δ≤β/(2*c):=(min_le_right _ _).trans (min_le_right _ _)
  let ε:ℝ:=min (δ/(8*c)) (min (q/4) (η/2))
  have hε:0<ε:=by dsimp [ε];positivity
  have hεδ:ε≤δ/(8*c):=min_le_left _ _
  have hεq:ε≤q/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hεη:ε≤η/2:=(min_le_right _ _).trans (min_le_right _ _)
  have hεc:4*c*ε≤δ/2:=by nlinarith only [(le_div_iff₀ (by positivity:0<8*c)).mp hεδ]
  have hKδ:K*δ≤η/2:=by
    have hh:δ*(2*(K+1))≤η:=(le_div_iff₀ (by positivity)).mp hδη
    nlinarith only [hh,hδ.le]
  refine ⟨ε,δ,hε,hδ,by linarith,by linarith,?_,?_⟩
  · have hh:δ*(2*c)≤β:=(le_div_iff₀ (by positivity)).mp hδβ
    dsimp [c] at hh
    nlinarith only [hh]
  · intro f hf
    obtain ⟨N,hN⟩:=exists_nat_gt (max 1 (2*(2*c*f+c)/δ))
    have hN1:1≤N:=by have hh: (1:ℝ)<N:=(le_max_left _ _).trans_lt hN;exact_mod_cast hh.le
    refine ⟨N,hN1,?_⟩
    intro n hn
    have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
    have hh:2*(2*c*f+c)/δ≤n:=(le_max_right _ _).trans (hN.le.trans hnR)
    have hbig:2*c*f+c≤δ*n/2:=by nlinarith only [(div_le_iff₀ hδ).mp hh]
    have hsmall:=mul_le_mul_of_nonneg_right hεc (show (0:ℝ)≤n by positivity)
    change 4*c*ε*n+2*c*f+c≤δ*n
    linarith

end Oberwolfach
