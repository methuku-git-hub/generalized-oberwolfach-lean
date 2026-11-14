module

public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! The full-selection mass error is eventually controlled by fixed-rate
bounds, in the required order: wheel and spacing parameters precede n. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_full_mass_error_eventually
    (m d:ℕ) (hd:0<d) (err:ℝ) (herr:0<err):
    ∃N:ℕ,∀n≥N,∀qsum frac ζ matchErr:ℝ,
      qsum≤1/8→frac≤1→0≤ζ→0≤matchErr→
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2→
      (n:ℝ)*qsum/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+
        matchErr*n*frac≤err*n:=by
  let M:ℝ:=(m:ℝ)+1
  have hM:0<M:=by dsimp [M];positivity
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (err/(4*M)) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n hn qsum frac ζ matchErr hq hf hζ he hrate
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hn0:0≤(n:ℝ):=by positivity
  have hp0:0≤(n:ℝ)^(3/4:ℝ):=by positivity
  have hPow0:=hN n hn
  have hPow:2*M*(n:ℝ)^(3/4:ℝ)≤err*n/2:=by
    have hh:=mul_le_mul_of_nonneg_left hPow0 (show 0≤2*M by positivity)
    have heq:2*M*(err/(4*M)*(n:ℝ))=err*n/2:=by field_simp <;> ring
    rw [heq] at hh
    simpa only [add_zero] using hh
  have hc:(((m+1)*d-1:ℕ):ℝ)≤M*d:=by
    have hh:((m+1)*d-1:ℕ)≤(m+1)*d:=Nat.sub_le _ _
    have hh':(((m+1)*d-1:ℕ):ℝ)≤(((m+1)*d:ℕ):ℝ):=by exact_mod_cast hh
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,M] using hh'
  have hx:0≤2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n:=by positivity
  have hProd:=mul_le_mul_of_nonneg_right hc hx
  have hQ:(n:ℝ)*qsum/d≤(n:ℝ)*(1/8:ℝ)/d:=by gcongr
  have hFrac:matchErr*n*frac≤matchErr*n:=by nlinarith [mul_nonneg he hn0]
  have heq:M*(d:ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)=
      2*M*(n:ℝ)^(3/4:ℝ)+M*(d:ℝ)*ζ*n:=by field_simp <;> ring
  rw [heq] at hProd
  have hRate:((1/(8*(d:ℝ))+M*(d:ℝ)*ζ+matchErr)*(n:ℝ))≤err*n/2:=by
    have hh:=mul_le_mul_of_nonneg_right hrate hn0
    dsimp [M] at hh ⊢
    nlinarith
  have hQeq:(n:ℝ)*(1/8:ℝ)/d=(1/(8*(d:ℝ)))*(n:ℝ):=by ring
  rw [hQeq] at hQ
  linarith
end Oberwolfach
