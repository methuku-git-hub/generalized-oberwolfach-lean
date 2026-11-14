module

public import Oberwolfach.ColourRoundLargeDegree

@[expose] public section

/-! Uniform absorption of all one-round errors, before rounding the next
list size and colour-degree bound to integers. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Filter
namespace Oberwolfach

theorem eventually_sublinear_affine_error
    (A C K δ η : ℝ) (hA : 0≤A) (hC : 0≤C) (hK : 0≤K)
    (hδ : 0<δ) (hη : 0<η) :
    ∃ N : ℕ, ∀ l : ℕ, N≤l → ∀ B : ℝ, B≤K*(l : ℝ)^(1-δ) →
      A*B+C≤η*l := by
  have ht : Tendsto (fun l : ℕ => (l : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (2*A*K/η))
  refine ⟨max 1 (max N₀ ⌈2*C/η⌉₊),?_⟩
  intro l hl B hB
  have hlpos : (0 : ℝ)<l := by exact_mod_cast (le_max_left _ _ |>.trans hl)
  have hp : 2*A*K/η≤(l : ℝ)^δ := hN₀ l ((le_max_left _ _).trans ((le_max_right _ _).trans hl))
  have hc : 2*C/η≤(l : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast
    ((le_max_right _ _).trans ((le_max_right _ _).trans hl) : ⌈2*C/η⌉₊≤l))
  have hprod : (l : ℝ)^δ*(l : ℝ)^(1-δ)=(l : ℝ) := by
    rw [← Real.rpow_add hlpos]
    convert Real.rpow_one (l : ℝ) using 1 <;> ring
  have hab : A*B≤η*l/2 := by
    have hp' : A*K≤(η/2)*(l : ℝ)^δ := by
      have hh := (div_le_iff₀ hη).mp hp
      linarith
    calc
      _ ≤ A*(K*(l : ℝ)^(1-δ)) := mul_le_mul_of_nonneg_left hB hA
      _ = (A*K)*(l : ℝ)^(1-δ) := by ring
      _ ≤ ((η/2)*(l : ℝ)^δ)*(l : ℝ)^(1-δ) := mul_le_mul_of_nonneg_right hp' (by positivity)
      _ = _ := by rw [mul_assoc,hprod];ring
  have hc' := (div_le_iff₀ hη).mp hc
  linarith

theorem colouring_round_errors_eventually_small
    (k : ℕ) (K δ η : ℝ) (hK : 0≤K) (hδ : 0<δ) (hη : 0<η) :
    ∃ N : ℕ, ∀ l : ℕ, N≤l → ∀ s B : ℕ, s≤l →
      (B : ℝ)≤K*(l : ℝ)^(1-δ) →
      1<l ∧ 4≤η*l ∧
      let t := η/(24*((k : ℝ)+1))*(l : ℝ)
      let ρ := (1-1/(l : ℝ))^(k*s)
      6*((k : ℝ)+1)*t+(l : ℝ)*
        ((2 : ℝ)^k*((k^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))≤η*l/2 ∧
      6*((k : ℝ)+1)*t+(s : ℝ)*
        (1/(l : ℝ)+ρ*(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1)))+
          (2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))≤η*l/2 := by
  let A : ℝ := (2 : ℝ)^k*((k^2*(2*k^2+k+2) : ℕ) : ℝ)
  let C : ℝ := (2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2) : ℕ) : ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  have hC : 0≤C := by dsimp [C];positivity
  obtain ⟨N₀,hN₀⟩ := eventually_sublinear_affine_error (A+C) (3+4*k) K δ (η/4)
    (by positivity) (by positivity) hK hδ (by positivity)
  refine ⟨max 2 (max N₀ ⌈4/η⌉₊),?_⟩
  intro l hl s B hs hB
  have hlN : 1<l := lt_of_lt_of_le (by norm_num : 1<2) ((le_max_left _ _).trans hl)
  have hlpos : (0 : ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hsl : (s : ℝ)≤l := by exact_mod_cast hs
  have hηl : 4≤η*l := by
    have hh : 4/η≤(l : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast
      ((le_max_right _ _).trans ((le_max_right _ _).trans hl) : ⌈4/η⌉₊≤l))
    have hh' := (div_le_iff₀ hη).mp hh
    linarith
  have herr := hN₀ l ((le_max_left _ _).trans ((le_max_right _ _).trans hl)) B hB
  have hcova := colouring_covariance_error_bound (k := k) hlN hs
  have hcova' := mul_le_mul_of_nonneg_left hcova (Nat.cast_nonneg s)
  have hcovup : (s : ℝ)*((3+4*(k : ℝ))/(l : ℝ))≤3+4*k := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlpos).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hsl
      (show (0 : ℝ)≤3+4*k by positivity)
  have ht : 6*((k : ℝ)+1)*(η/(24*((k : ℝ)+1))*(l : ℝ))=η*l/4 := by
    have hkpos : (0 : ℝ)<(k : ℝ)+1 := by positivity
    field_simp <;> ring
  have hlist : (l : ℝ)*((2 : ℝ)^k*((k^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))=A*B := by
    rw [mul_div_cancel₀ _ hlpos.ne']
    dsimp [A];push_cast;ring
  have hpair : (s : ℝ)*((2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))≤C*B := by
    have he : (2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2)*B : ℕ) : ℝ)=C*B := by
      dsimp [C];rw [Nat.cast_mul];ring
    rw [he,← mul_div_assoc]
    apply (div_le_iff₀ hlpos).mpr
    have hh := mul_le_mul_of_nonneg_left hsl (mul_nonneg hC (Nat.cast_nonneg B))
    nlinarith
  refine ⟨hlN,hηl,?_⟩
  dsimp only
  rw [ht,hlist]
  constructor
  · nlinarith [mul_nonneg hC (Nat.cast_nonneg B)]
  · have hcovfinal := hcova'.trans hcovup
    rw [mul_add]
    nlinarith [mul_nonneg hA (Nat.cast_nonneg B)]

end Oberwolfach
