module

public import Oberwolfach.LongReservedListFirstVortexMargins

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_continuation_parameters
    (γ pstar:ℝ) (hγ:0<γ) (hp:0<pstar):
    ∃β δ:ℝ,0<β ∧ β≤1 ∧ 0<δ ∧ δ≤(β/200)^2 ∧ δ≤1/100 ∧
    ∃dMin L₀:ℕ,
      (∀m:ℕ,L₀≤m→4/(m:ℝ)≤δ/4) ∧
      ∀(ε δlocal lamMax ζMax:ℝ),0<ε→0<δlocal→0<lamMax→0<ζMax→
      ∃lam ζ:ℝ,0<lam ∧ lam≤1/100 ∧ lam≤lamMax ∧ lam≤δlocal*ε/32 ∧ 0<ζ ∧ ζ≤ζMax ∧ ζ≤lam/3 ∧
      ∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ) ∧
        (lam+2*ζ)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n :=by
  obtain ⟨β,hβ,hβ1,dMin,hList⟩:=long_reserved_list_first_vortex_margins γ pstar hγ hp
  let δ:ℝ:=min ((β/200)^2) (1/100)
  have hδ:0<δ:=by dsimp [δ];positivity
  obtain ⟨L₀,hL₀⟩:=exists_nat_gt (16/δ)
  refine ⟨β,δ,hβ,hβ1,hδ,min_le_left _ _,min_le_right _ _,dMin,L₀,?_,hList⟩
  intro m hm
  have hmR:(16/δ)<(m:ℝ):=lt_of_lt_of_le hL₀ (by exact_mod_cast hm)
  have hm0:0<(m:ℝ):=lt_trans (by positivity : 0<16/δ) hmR
  have hprod:16<δ*m:=by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hmR
  apply (div_le_iff₀ hm0).2
  nlinarith

theorem spacing_threshold_from_small_theta
    (dMin d:ℕ) (hd:0<d) (θ:ℝ) (hθ:0<θ) (hsmall:θ≤1/((dMin:ℝ)+1))
    (hinv:1/(d:ℝ)≤θ/1024):
    dMin≤d:=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hden:0<(dMin:ℝ)+1:=by positivity
  by_contra hnot
  have hlt:(d:ℝ)<(dMin:ℝ)+1:=by exact_mod_cast (show d<dMin+1 by omega)
  have hprod:1≤(θ/1024)*(d:ℝ):=(div_le_iff₀ hdR).mp hinv
  have hmul:=mul_le_mul_of_nonneg_right hsmall hdR.le
  have hdiv:(d:ℝ)/((dMin:ℝ)+1)<1:=(div_lt_one hden).2 hlt
  have heq:(1/((dMin:ℝ)+1))*(d:ℝ)=(d:ℝ)/((dMin:ℝ)+1):=by ring
  rw [heq] at hmul
  nlinarith
end Oberwolfach
