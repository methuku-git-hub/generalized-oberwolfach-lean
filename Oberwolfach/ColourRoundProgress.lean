module

public import Oberwolfach.ColourRoundNumerics

@[expose] public section

/-! Robust progress inequalities for the finite colouring iteration.
The losses in both list size and colour degree are retained explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace Oberwolfach

theorem colouring_round_ratio_progress
    {k : ℕ} (hk : 0<k) {l s ρ a b ε η M r l' s' : ℝ}
    (hs : 0<s) (ha : 0<a) (ha1 : a≤1) (hb : 0<b)
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0≤η)
    (hρ : a≤ρ ∧ ρ≤1) (hr : 1+ε≤r) (hrM : r≤M)
    (hl : r*s≤l) (hlM : l≤M*s)
    (hκ : b≤1-s*ρ/l)
    (herror : η*M*(M+2)≤(a*ε/4)*b^(k-1))
    (hl' : l*(1-s*ρ/l)^k-η*l≤l')
    (hs' : s'≤s*(1-ρ)*(1-s*ρ/l)^(k-1)+η*l) :
    (r+a*ε/4)*s'≤l' := by
  let c := a*ε/4
  have hc : 0<c := by dsimp [c];positivity
  have hc1 : c≤1 := by
    dsimp [c]
    nlinarith [mul_le_mul ha1 hε1 hε.le (by norm_num : (0 : ℝ)≤1)]
  have hr0 : 0≤r := by linarith
  have hM0 : 0≤M := hr0.trans hrM
  have hl0 : 0<l := lt_of_lt_of_le (mul_pos (by linarith : 0<r) hs) hl
  have hρ0 : 0≤ρ := ha.le.trans hρ.1
  have hpow : b^(k-1)≤(1-s*ρ/l)^(k-1) := pow_le_pow_left₀ hb.le hκ _
  have hp0 : 0≤(1-s*ρ/l)^(k-1) := pow_nonneg (hb.le.trans hκ) _
  have hcoeff : 3*c≤(r-1)*ρ-c*(1-ρ) := by
    have h₁ := mul_le_mul_of_nonneg_right (show ε≤r-1 by linarith) hρ0
    have h₂ := mul_le_mul_of_nonneg_left hρ.1 hε.le
    have h₃ := mul_nonneg hc.le hρ0
    dsimp [c] at *
    nlinarith
  have hmargin : 3*c*s*b^(k-1)≤
      l*(1-s*ρ/l)^k-(r+c)*s*(1-ρ)*(1-s*ρ/l)^(k-1) := by
    have hid : l*(1-s*ρ/l)^k-(r+c)*s*(1-ρ)*(1-s*ρ/l)^(k-1)=
        (l-r*s+s*((r-1)*ρ-c*(1-ρ)))*(1-s*ρ/l)^(k-1) := by
      rw [show (1-s*ρ/l)^k=(1-s*ρ/l)^(k-1)*(1-s*ρ/l) from by
        rw [← pow_succ,Nat.sub_add_cancel (by omega : 1≤k)]]
      have he : l*(1-s*ρ/l)=l-s*ρ := by field_simp
      calc
        _ = (l*(1-s*ρ/l)-(r+c)*s*(1-ρ))*(1-s*ρ/l)^(k-1) := by ring
        _ = _ := by rw [he];ring
    rw [hid]
    calc
      _ ≤ (3*c*s)*(1-s*ρ/l)^(k-1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (l-r*s+s*((r-1)*ρ-c*(1-ρ)))*(1-s*ρ/l)^(k-1) := by
        apply mul_le_mul_of_nonneg_right _ hp0
        have hh := mul_le_mul_of_nonneg_left hcoeff hs.le
        nlinarith
  have hloss : (r+c+1)*η*l≤c*s*b^(k-1) := by
    calc
      _ ≤ (M+2)*η*l := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hη) hl0.le
      _ ≤ (M+2)*η*(M*s) := mul_le_mul_of_nonneg_left hlM (by positivity)
      _ = (η*M*(M+2))*s := by ring
      _ ≤ (c*b^(k-1))*s := mul_le_mul_of_nonneg_right herror hs.le
      _ = _ := by ring
  have hs'' := mul_le_mul_of_nonneg_left hs' (show 0≤r+c by positivity)
  have hposit : 0≤c*s*b^(k-1) := by positivity
  change (r+c)*s'≤l'
  nlinarith

theorem colouring_round_list_lower
    {k : ℕ} {l b κ η l' : ℝ} (hl : 0≤l) (hb : 0≤b) (hκ : b≤κ)
    (hη : η≤b^k/2) (hl' : l*κ^k-η*l≤l') :
    (b^k/2)*l≤l' := by
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hκ k) hl
  have he := mul_le_mul_of_nonneg_right hη hl
  nlinarith

end Oberwolfach
