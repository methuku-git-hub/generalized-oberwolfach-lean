module

public import Oberwolfach.ColourRoundNumerics
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Polynomial bounds for the two numerical denominators in the
simultaneous colouring event. The bounds are uniform in the number of edges. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace Oberwolfach

theorem colouring_variance_denominator_bound {k l B s : ℕ} (hs : s≤l) :
    12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ)≤
      (12*(k : ℝ)+4*(2+((k : ℝ)+3)*k)*(3+3*k))*(l : ℝ)*((B : ℝ)+1) := by
  push_cast
  have hsl : (s : ℝ)≤l := by exact_mod_cast hs
  have hx : 2+((k : ℝ)+3)*((k : ℝ)*B)≤
      (2+((k : ℝ)+3)*k)*((B : ℝ)+1) := by
    have hkR : (0 : ℝ)≤k := Nat.cast_nonneg _
    have hBR : (0 : ℝ)≤B := Nat.cast_nonneg _
    nlinarith
  have h₁ : 12*(k : ℝ)*(l : ℝ)≤12*(k : ℝ)*(l : ℝ)*((B : ℝ)+1) := by
    have h := mul_nonneg (show 0≤12*(k : ℝ)*(l : ℝ) by positivity) (Nat.cast_nonneg B)
    nlinarith
  calc
    _ ≤ 12*(k : ℝ)*(l : ℝ)+
      4*((2+((k : ℝ)+3)*k)*((B : ℝ)+1))*(3+3*k)*(l : ℝ) := by gcongr
    _ ≤ 12*(k : ℝ)*(l : ℝ)*((B : ℝ)+1)+
      4*((2+((k : ℝ)+3)*k)*((B : ℝ)+1))*(3+3*k)*(l : ℝ) := by linarith
    _ = _ := by ring

theorem colouring_dependency_polynomial_bound {k l s d : ℕ} (hl : 0<l) (hs : s≤l)
    {K : ℝ} (hK : 0≤K) (hd : (d : ℝ)≤K*(l : ℝ)^2) :
    ((s*(1+k*l)*(d+1)^4 : ℕ) : ℝ)≤
      ((k : ℝ)+1)*(K+1)^4*(l : ℝ)^10 := by
  have hl1 : (1 : ℝ)≤l := by exact_mod_cast hl
  have hsl : (s : ℝ)≤l := by exact_mod_cast hs
  have h₁ : 1+(k : ℝ)*l≤((k : ℝ)+1)*l := by linarith
  have h₂ : (d : ℝ)+1≤(K+1)*(l : ℝ)^2 := by nlinarith
  push_cast
  calc
    _ ≤ (l : ℝ)*(((k : ℝ)+1)*l)*((K+1)*(l : ℝ)^2)^4 := by gcongr
    _ = _ := by ring

end Oberwolfach
