module

public import Mathlib.Tactic

@[expose] public section

/-! Uniform integer scales for rounding fractional resource weights.
All order bounds precede the graph, its edge identifiers and its tests. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Oberwolfach

theorem resource_rounding_order (r : ℕ) (η a : ℝ) (hη : 0<η) (ha : 0<a) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n → 2≤n ∧ r+1≤n ∧ 4≤η*n ∧ 1≤a*n := by
  refine ⟨max (max 2 (r+1)) (max ⌈4/η⌉₊ ⌈1/a⌉₊),?_⟩
  intro n hn
  have hcη : ⌈4/η⌉₊≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hca : ⌈1/a⌉₊≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnη : (4/η : ℝ)≤n := (Nat.le_ceil (4/η)).trans (by exact_mod_cast hcη)
  have hna : (1/a : ℝ)≤n := (Nat.le_ceil (1/a)).trans (by exact_mod_cast hca)
  refine ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hn),
    (le_max_right _ _).trans ((le_max_left _ _).trans hn),?_,?_⟩
  · nlinarith [(div_le_iff₀ hη).mp hnη]
  · nlinarith [(div_le_iff₀ ha).mp hna]

theorem resource_rounding_scales (n B : ℕ) (η : ℝ)
    (hn : 2≤n) (hη : 0<η) (hηsmall : η≤1/100) (hηn : 4≤η*n) :
    let T := n^(2*B+2)
    let D := ⌈(1+η)*(T : ℝ)⌉₊
    n≤T ∧ 1≤η*T ∧ 4*(n : ℝ)^(2*B)≤η*T ∧
      (1+η)*(T : ℝ)≤D ∧ (D : ℝ)≤(1+2*η)*T ∧ D≤2*T ∧ n≤D ∧
      D≤n^(3*B+4) := by
  dsimp only
  let T := n^(2*B+2)
  let D := ⌈(1+η)*(T : ℝ)⌉₊
  have hn1 : 1≤n := by omega
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn1
  have hTn : n≤T := by
    calc
      _ = n^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hn1 (by omega)
  have hTη : 4≤η*T := hηn.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hTn) hη.le)
  have hT0 : 0<T := lt_of_lt_of_le (by omega : 0<n) hTn
  have hTR : (0 : ℝ)<T := by exact_mod_cast hT0
  have hsup : 4*(n : ℝ)^(2*B)≤η*T := by
    have hh := mul_le_mul_of_nonneg_right hηn (pow_nonneg (Nat.cast_nonneg n) (2*B))
    have hh' := mul_le_mul_of_nonneg_right hnR
      (show 0≤η*(n : ℝ)^(2*B)*n by positivity)
    have heq : (T : ℝ)=(n : ℝ)^(2*B)*n^2 := by
      simp only [T,pow_add,Nat.cast_mul,Nat.cast_pow]
    rw [heq]
    nlinarith
  have hDlo : (1+η)*(T : ℝ)≤D := Nat.le_ceil _
  have hDhi : (D : ℝ)≤(1+2*η)*T := by
    have hh := Nat.ceil_lt_add_one (show 0≤(1+η)*(T : ℝ) by positivity)
    change (D : ℝ)<_ at hh
    nlinarith
  have hD2 : D≤2*T := by
    have hh : (D : ℝ)≤2*(T : ℝ) := by nlinarith [mul_nonneg (show 0≤1-2*η by linarith) hTR.le]
    exact_mod_cast hh
  have hTD : T≤D := by
    have hh : (T : ℝ)≤D := by nlinarith
    exact_mod_cast hh
  have hDbound : D≤n^(3*B+4) := by
    calc
      D ≤ 2*T := hD2
      _ ≤ n*T := Nat.mul_le_mul_right T hn
      _ = n^(2*B+3) := by dsimp [T];rw [← pow_succ']
      _ ≤ _ := Nat.pow_le_pow_right hn1 (by omega)
  exact ⟨hTn,by linarith,hsup,hDlo,hDhi,hD2,hTn.trans hTD,hDbound⟩

theorem resource_padding_polynomial_card (n B r N C : ℕ)
    (hn : 2≤n) (hr : r+1≤n) (hN : N≤n^B) (hC : C≤n^(2*B+2)*N) :
    N+r*C≤n^(3*B+4) := by
  have hn1 : 1≤n := by omega
  have hT1 : 1≤n^(2*B+2) := one_le_pow₀ hn1
  calc
    N+r*C ≤ N+r*(n^(2*B+2)*N) := Nat.add_le_add_left (Nat.mul_le_mul_left r hC) N
    _ ≤ n^(2*B+2)*N+r*(n^(2*B+2)*N) := Nat.add_le_add_right (by nlinarith) _
    _ = (r+1)*(n^(2*B+2)*N) := by ring
    _ ≤ n*(n^(2*B+2)*n^B) := Nat.mul_le_mul hr (Nat.mul_le_mul_left _ hN)
    _ = n^(3*B+3) := by rw [← pow_add,← pow_succ'];congr 1 <;> omega
    _ ≤ _ := Nat.pow_le_pow_right hn1 (by omega)

theorem resource_test_polynomial_card (n B s t : ℕ) (hn : 2≤n)
    (hs : s≤n^B) (ht : t≤n^B) : s+t≤n^(3*B+4) := by
  calc
    _ ≤ n^B+n^B := Nat.add_le_add hs ht
    _ = 2*n^B := by ring
    _ ≤ n*n^B := Nat.mul_le_mul_right _ hn
    _ = n^(B+1) := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem resource_sparse_support_bound (n B N A : ℕ) (hn : 1≤n)
    (hN : N≤n^B) (hA : A≤n^B) : N+N^2+A+1≤4*n^(2*B) := by
  have hp : 1≤n^B := one_le_pow₀ hn
  have hNsq := Nat.pow_le_pow_left hN 2
  have hpeq : (n^B)^2=n^(2*B) := by rw [← pow_mul];congr 1;omega
  rw [← hpeq]
  nlinarith

end Oberwolfach
