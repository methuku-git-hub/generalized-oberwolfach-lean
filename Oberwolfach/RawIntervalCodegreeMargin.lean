module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Fixed constants are chosen before the graph order: the all-pairs failure
probability tends to zero at the rate needed by the first cover-down. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem raw_interval_codegree_margin
    (d:ℕ) (ω s₀ ζ:ℝ) (hω:0<ω) (hs₀:0<s₀) (hζ:0<ζ):
    ∃ N:ℕ,∀ n m:ℕ,N≤n→ω*(n:ℝ)≤m→
      let α:ℝ:=(5/32:ℝ)*s₀^2*ω
      let t:ℝ:=(5/16:ℝ)*s₀^2*m;
      0<t ∧ 0<α ∧ 2*α*n+t≤(5/8:ℝ)*s₀^2*m ∧
      (n:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*m))))≤ζ:=by
  let a:ℝ:=(5/16:ℝ)*s₀^2
  let c:ℝ:=a^2*ω/((4*(d:ℝ)+3)^2)
  have ha:0<a:=by dsimp [a];positivity
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (2:ℝ) 2 (c:=c) (p:=1) hc (by norm_num) 1
  obtain ⟨M,hM⟩:=exists_nat_gt (1/ζ)
  refine ⟨max N (max (M+1) 1),?_⟩
  intro n m hn hmn α t
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hn1:1≤n:=le_trans (le_trans (le_max_right (M+1) 1) (le_max_right N _)) hn
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hmpos:(0:ℝ)<m:=lt_of_lt_of_le (mul_pos hω hnpos) hmn
  have hmne:(m:ℝ)≠0:=ne_of_gt hmpos
  have hαpos:0<α:=by dsimp [α];positivity
  have htpos:0<t:=by dsimp [t];positivity
  have hαeq:2*α=a*ω:=by dsimp [α,a];ring
  have hteq:t=a*m:=by rfl
  have hmargin:2*α*n+t≤(5/8:ℝ)*s₀^2*m:=by
    calc
      2*α*n+t = a*(ω*n)+a*m := by rw [hteq];dsimp [α,a];ring
      _ ≤ a*m+a*m := by
        have hh:=mul_le_mul_of_nonneg_left hmn ha.le
        linarith
      _ = (5/8:ℝ)*s₀^2*m := by dsimp [a];ring
  have harg:-2*t^2/((4*(d:ℝ)+3)^2*(2*m))=-(a^2/((4*(d:ℝ)+3)^2))*m:=by
    rw [hteq]
    field_simp
    <;> ring
  have hargle:-2*t^2/((4*(d:ℝ)+3)^2*(2*m))≤ -c*n:=by
    have heq:c*n=(a^2/((4*(d:ℝ)+3)^2))*(ω*n):=by dsimp [c];ring
    rw [harg,show -c*n=-(c*n) by ring,heq]
    have hh:=mul_le_mul_of_nonneg_left hmn (show 0≤a^2/((4*(d:ℝ)+3)^2) by positivity)
    linarith
  have hb:=hN n hnN
  simp only [Real.rpow_ofNat,Real.rpow_one,pow_one] at hb
  have hexp:=Real.exp_le_exp.mpr hargle
  have hsmall:(1:ℝ)/n≤ζ:=by
    apply (div_le_iff₀ hnpos).2
    have hMn:(M:ℝ)<n:=by exact_mod_cast (show M<n by have h:=le_trans (le_trans (le_max_left (M+1) 1) (le_max_right N _)) hn;omega)
    have hM':(1:ℝ)<ζ*M:=by simpa [mul_comm] using (div_lt_iff₀ hζ).mp hM
    nlinarith
  have herr:(n:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*m))))≤ζ:=by
    have h:=mul_le_mul_of_nonneg_left hexp (show 0≤2*(n:ℝ)^2 by positivity)
    nlinarith [hb,hsmall]
  exact ⟨htpos,hαpos,hmargin,herr⟩
end Oberwolfach
