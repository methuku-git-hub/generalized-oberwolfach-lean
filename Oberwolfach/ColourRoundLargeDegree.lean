module

public import Oberwolfach.ColourRoundPolynomialBounds

@[expose] public section

/-! One order threshold suffices for every permitted colour degree and
codegree in a round. It is independent of the hypergraph and its edge set. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Filter
namespace Oberwolfach

theorem colouring_round_eventually_valid
    (k : ℕ) (hk : 0<k) (K δ τ : ℝ)
    (hK : 1≤K) (hδ : 0<δ) (hδ1 : δ≤1) (hτ : 0<τ) :
    ∃ N : ℕ, ∀ l : ℕ, N≤l → ∀ s B d : ℕ, 0<s → s≤l →
      (B : ℝ)≤K*(l : ℝ)^(1-δ) → (d : ℝ)≤K*(l : ℝ)^2 →
      1<l ∧ 2*(k : ℝ)^4*B≤l ∧
      let W := 12*(k : ℝ)*l+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*s
      (l : ℝ)*4*Real.exp (-((τ*l)^2/W))≤τ*l ∧
      8*((k : ℝ)+1)*Real.exp (-((τ*l)^2/W))≤
        1/(4*((s*(1+k*l)*(d+1)^4 : ℕ) : ℝ)) := by
  let A : ℝ := 12*k+4*(2+((k : ℝ)+3)*k)*(3+3*k)
  have hA : 0<A := by dsimp [A];positivity
  have hKpos : 0<K+1 := by linarith
  let c : ℝ := τ^2/(A*(K+1))
  have hc : 0<c := div_pos (sq_pos_of_pos hτ) (mul_pos hA hKpos)
  let P : ℝ := ((k : ℝ)+1)*(K+1)^4
  have hP : 0<P := by dsimp [P];positivity
  obtain ⟨N₁,hN₁⟩ := eventually_stretchedExp_le_inv_pow (4/τ) 0 hc hδ 0
  obtain ⟨N₂,hN₂⟩ := eventually_stretchedExp_le_inv_pow (32*((k : ℝ)+1)*P) 0 hc hδ 10
  have ht : Tendsto (fun l : ℕ => (l : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (2*(k : ℝ)^4*K))
  refine ⟨max 2 (max N₁ (max N₂ N₃)),?_⟩
  intro l hl s B d hs hsl hB hd
  have hl2 : 2≤l := (le_max_left _ _).trans hl
  have hlpos : (0 : ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hl1 : (1 : ℝ)≤l := by exact_mod_cast (show 1≤l by omega)
  have hle₁ : N₁≤l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hle₂ : N₂≤l := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hl))
  have hle₃ : N₃≤l := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hl))
  have hpow := hN₃ l hle₃
  have hproduct : (l : ℝ)^δ*(l : ℝ)^(1-δ)=(l : ℝ) := by
    rw [← Real.rpow_add hlpos];ring_nf;rw [Real.rpow_one]
  have hcodeg : 2*(k : ℝ)^4*B≤l := by
    calc
      _ ≤ 2*(k : ℝ)^4*(K*(l : ℝ)^(1-δ)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (2*(k : ℝ)^4*K)*(l : ℝ)^(1-δ) := by ring
      _ ≤ (l : ℝ)^δ*(l : ℝ)^(1-δ) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := hproduct
  refine ⟨by omega,hcodeg,?_⟩
  dsimp only
  let W : ℝ := 12*(k : ℝ)*l+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*s
  have hkR : (0 : ℝ)<k := Nat.cast_pos.mpr hk
  have hW : 0<W := by dsimp [W];positivity
  have hpow1 : (1 : ℝ)≤(l : ℝ)^(1-δ) := Real.one_le_rpow hl1 (by linarith)
  have hB1 : (B : ℝ)+1≤(K+1)*(l : ℝ)^(1-δ) := by nlinarith
  have hWbound : W≤A*(K+1)*(l : ℝ)^(2-δ) := by
    calc
      _ ≤ A*(l : ℝ)*((B : ℝ)+1) := colouring_variance_denominator_bound hsl
      _ ≤ A*(l : ℝ)*((K+1)*(l : ℝ)^(1-δ)) :=
        mul_le_mul_of_nonneg_left hB1 (by positivity)
      _ = A*(K+1)*(l : ℝ)^(2-δ) := by
        rw [show 2-δ=1+(1-δ) by ring,Real.rpow_add hlpos,Real.rpow_one]
        ring
  have hprod2 : (l : ℝ)^δ*(l : ℝ)^(2-δ)=(l : ℝ)^2 := by
    rw [← Real.rpow_add hlpos]
    convert Real.rpow_two (l : ℝ) using 1 <;> ring
  have hexponent : c*(l : ℝ)^δ≤(τ*l)^2/W := by
    apply (le_div_iff₀ hW).mpr
    calc
      _ ≤ (c*(l : ℝ)^δ)*(A*(K+1)*(l : ℝ)^(2-δ)) :=
        mul_le_mul_of_nonneg_left hWbound (by positivity)
      _ = τ^2*((l : ℝ)^δ*(l : ℝ)^(2-δ)) := by dsimp [c];field_simp <;> ring
      _ = _ := by rw [hprod2];ring
  have hexp : Real.exp (-((τ*l)^2/W))≤Real.exp (-c*(l : ℝ)^δ) := by
    simpa only [neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hexponent)
  have hsmall : 4*Real.exp (-c*(l : ℝ)^δ)≤τ := by
    have hh := hN₁ l hle₁
    simp only [Real.rpow_zero,pow_zero,div_one,mul_one] at hh
    have hh' : 4*Real.exp (-c*(l : ℝ)^δ)/τ≤1 := by simpa only [div_mul_eq_mul_div] using hh
    exact (div_le_one hτ).mp hh'
  have hrare : 32*((k : ℝ)+1)*P*Real.exp (-c*(l : ℝ)^δ)*(l : ℝ)^10≤1 := by
    have hh := hN₂ l hle₂
    simp only [Real.rpow_zero,mul_one] at hh
    exact (le_div_iff₀ (pow_pos hlpos _)).mp hh
  have hden := colouring_dependency_polynomial_bound (k := k) (by omega : 0<l) hsl (by linarith : 0≤K) hd
  have hdenpos : (0 : ℝ)<4*((s*(1+k*l)*(d+1)^4 : ℕ) : ℝ) := by positivity
  constructor
  · change (l : ℝ)*4*Real.exp (-((τ*l)^2/W))≤τ*l
    have hh := mul_le_mul_of_nonneg_left hexp (show 0≤4*(l : ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_right hsmall hlpos.le
    nlinarith
  · change 8*((k : ℝ)+1)*Real.exp (-((τ*l)^2/W))≤_
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ (8*((k : ℝ)+1)*Real.exp (-c*(l : ℝ)^δ))*(4*(P*(l : ℝ)^10)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hexp (by positivity)
        · exact mul_le_mul_of_nonneg_left hden (by norm_num)
        · positivity
        · positivity
      _ ≤ 1 := by nlinarith

end Oberwolfach
