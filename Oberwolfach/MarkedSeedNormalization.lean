module

public import Mathlib.Tactic

@[expose] public section

/-! Uniform two-sided bounds for the fixed marked seed coefficients. The
reference degree D is supplied and is not replaced by a sampled degree. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Oberwolfach

theorem marked_seed_coefficient_bounds (m : ℕ) (hm : 1≤m)
    (n D p k s a B w pstar : ℝ)
    (hn : 0<n) (hDlo : n/2≤D) (hDhi : D≤2*n)
    (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s≤1) (ha : 0≤a) (hB : 0≤B)
    (hwlo : a/n^(m-1)≤w) (hwhi : w≤B/n^(m-1)) :
    (a/2)/n^m≤w/(D*p^m*k*s^m) ∧
      w/(D*p^m*k*s^m)≤(2*B/pstar^(2*m+1))/n^m := by
  have hp0 := hpstar.trans_le hp
  have hk0 := hpstar.trans_le hk
  have hs0 := hpstar.trans_le hs
  have hD0 : 0<D := (half_pos hn).trans_le hDlo
  have hw0 : 0≤w := (by positivity : 0≤a/n^(m-1)).trans hwlo
  have hpow : n^m=n^(m-1)*n := by rw [← pow_succ];congr 1;omega
  have hupper : p^m*k*s^m≤1 := by
    have hp' := pow_le_one₀ hp0.le hp1 (n:=m)
    have hs' := pow_le_one₀ hs0.le hs1 (n:=m)
    calc
      _ ≤ 1*1*1 := mul_le_mul (mul_le_mul hp' hk1 hk0.le (by norm_num)) hs'
        (pow_nonneg hs0.le _) (by norm_num)
      _ = 1 := by norm_num
  have hlower : pstar^(2*m+1)≤p^m*k*s^m := by
    calc
      _ = pstar^m*pstar*pstar^m := by rw [← pow_succ,← pow_add];congr 1;omega
      _ ≤ _ := mul_le_mul (mul_le_mul (pow_le_pow_left₀ hpstar.le hp m) hk hpstar.le
        (pow_nonneg hp0.le _)) (pow_le_pow_left₀ hpstar.le hs m)
        (pow_nonneg hpstar.le _) (mul_nonneg (pow_nonneg hp0.le _) hk0.le)
  have hdenlo : (n/2)*pstar^(2*m+1)≤D*p^m*k*s^m := by
    convert mul_le_mul hDlo hlower (by positivity) hD0.le using 1 <;> ring
  have hdenhi : D*p^m*k*s^m≤2*n := by
    calc
      _ = D*(p^m*k*s^m) := by ring
      _ ≤ D*1 := mul_le_mul_of_nonneg_left hupper hD0.le
      _ ≤ _ := by simpa using hDhi
  constructor
  · calc
      _ = (a/n^(m-1))/(2*n) := by rw [hpow];field_simp
      _ ≤ w/(D*p^m*k*s^m) := div_le_div₀ (by positivity) hwlo (by positivity) hdenhi
  · calc
      _ ≤ (B/n^(m-1))/((n/2)*pstar^(2*m+1)) :=
        div_le_div₀ (by positivity) hwhi (by positivity) hdenlo
      _ = _ := by rw [hpow];field_simp

end Oberwolfach
