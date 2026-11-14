module

public import Oberwolfach.BinomialPowerTailMargins

@[expose] public section

/-! One threshold handles every fixed restriction of sufficiently large
order, even when that order is much smaller than the ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach

theorem uniform_binomial_restriction_tail (K a b : ℝ) (hK : 0≤K) (ha : 0<a) (hb : 0<b) (L : ℕ) :
    ∃ m N : ℕ,1≤m ∧ 1≤N ∧ ∀ n : ℕ,N≤n → ∀ M : ℕ,m≤M →
    ∀ p : ℝ,0≤p → p≤K*(n:ℝ)^(-b) →
      (M.choose (Nat.ceil (a*M)):ℝ)*p^(Nat.ceil (a*M))≤1/(n:ℝ)^L := by
  obtain ⟨N,hN1,hN⟩ := eventually_binomial_deletion_tail K a b hK ha hb
  let c := a*b/2
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨max 1 (Nat.ceil ((L:ℝ)/c)),N,le_max_left _ _,hN1,?_⟩
  intro n hn M hM p hp hrate
  have hnR : (1:ℝ)≤n := by exact_mod_cast hN1.trans hn
  have hLM : (L:ℝ)≤c*M := by
    have hceil : (L:ℝ)/c≤(M:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil ((L:ℝ)/c)≤M by omega))
    have hh := (div_le_iff₀ hc).mp hceil
    linarith
  have hh := hN n hn M (Nat.ceil (a*M)) p hp hrate (Nat.le_ceil _)
  have hpow : (n:ℝ)^(-c*M)≤(n:ℝ)^(-(L:ℝ)) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  apply hh.trans
  simpa only [Real.rpow_neg (by linarith : (0:ℝ)≤n),Real.rpow_natCast,one_div] using hpow

theorem retention_restriction_union_margin (d C Q n : ℕ) (hn : 2*(d+2)≤n)
    (I m : ℕ) (hI : I≤n^C) (hm : m≤n) :
    (I:ℝ)*(m+(d+1:ℕ)*n)*(1/(n:ℝ)^(C+Q+3))≤1/(2*(n:ℝ)^Q) := by
  have hn2 : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
  have hnpos : (0:ℝ)<n := by linarith
  have hd : (2:ℝ)*(d+2)≤n := by exact_mod_cast hn
  have hsize : (I:ℝ)*(m+(d+1:ℕ)*n)≤(d+2)*(n:ℝ)^(C+1) := by
    have hiR : (I:ℝ)≤(n:ℝ)^C := by exact_mod_cast hI
    have hmR : (m:ℝ)≤n := by exact_mod_cast hm
    calc
      _ ≤ (n:ℝ)^C*(n+(d+1:ℕ)*n) := mul_le_mul hiR (by gcongr) (by positivity) (by positivity)
      _ = _ := by simp only [Nat.cast_add,Nat.cast_one,pow_succ];ring
  have heq : ((d:ℝ)+2)*(n:ℝ)^(C+1)*(1/(n:ℝ)^(C+Q+3))=
      ((d:ℝ)+2)/(n:ℝ)^2*(1/(n:ℝ)^Q) := by
    have hex : C+Q+3=(C+1)+Q+2 := by omega
    rw [hex,pow_add,pow_add]
    field_simp
    simp only [pow_add,pow_succ]
  have hconst : ((d:ℝ)+2)/(n:ℝ)^2≤1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hnSq : (n:ℝ)≤(n:ℝ)^2 := by nlinarith
    nlinarith
  calc
    _ ≤ (d+2)*(n:ℝ)^(C+1)*(1/(n:ℝ)^(C+Q+3)) := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = _ := heq
    _ ≤ (1/2)*(1/(n:ℝ)^Q) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by ring

end Oberwolfach
