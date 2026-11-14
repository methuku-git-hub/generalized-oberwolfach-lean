module

public import Oberwolfach.AbsorberRestrictionScales

@[expose] public section

/-! The deletion tolerance precedes the bounded forbidden-edge allowance.
Only the ambient order threshold is allowed to depend on that allowance. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach

theorem ordinary_profile_deletion_margins (β a τ K L : ℝ)
    (hβ : 0<β) (ha : 0<a) (hτ : 0<τ) (hK : 0≤K) (hL : 0≤L) :
    ∃ ε : ℝ,0<ε ∧ ε≤β/2 ∧ ∀ f : ℕ,∃ N : ℕ,1≤N ∧
      ∀ n : ℕ,N≤n → ∀ z e : ℕ,(z:ℝ)≤ε*n → e≤f →
        ((z+e:ℕ):ℝ)*K/n≤τ/2 ∧
        ((z+e:ℕ):ℝ)*L≤(a/2)*n := by
  let ε := min (β/2) (min (τ/(4*(K+1))) (a/(4*(L+1))))
  have hε : 0<ε := by dsimp [ε];positivity
  have hεK : 2*ε*K≤τ/2 := by
    have hh : ε≤τ/(4*(K+1)) := (min_le_right _ _).trans (min_le_left _ _)
    have ht := (le_div_iff₀ (by positivity : (0:ℝ)<4*(K+1))).mp hh
    nlinarith only [ht,hε]
  have hεL : 2*ε*L≤a/2 := by
    have hh : ε≤a/(4*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have ht := (le_div_iff₀ (by positivity : (0:ℝ)<4*(L+1))).mp hh
    nlinarith only [ht,hε]
  refine ⟨ε,hε,min_le_left _ _,?_⟩
  intro f
  obtain ⟨N,hN⟩ := exists_nat_gt ((f:ℝ)/ε)
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro n hn z e hz he
  have hn1 : 1≤n := (le_max_left 1 N).trans hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hNn : (N:ℝ)≤n := by exact_mod_cast (le_max_right 1 N).trans hn
  have hf : (f:ℝ)≤ε*n := by
    have hh := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hN hNn)
    linarith
  have heR : (e:ℝ)≤ε*n := (Nat.cast_le.mpr he).trans hf
  have hsum : ((z+e:ℕ):ℝ)≤2*ε*n := by push_cast;linarith only [hz,heR]
  constructor
  · apply (div_le_iff₀ hnR).mpr
    have hh := mul_le_mul_of_nonneg_right hsum hK
    have ht := mul_le_mul_of_nonneg_right hεK hnR.le
    nlinarith only [hh,ht]
  · have hh := mul_le_mul_of_nonneg_right hsum hL
    have ht := mul_le_mul_of_nonneg_right hεL hnR.le
    nlinarith only [hh,ht]

end Oberwolfach
