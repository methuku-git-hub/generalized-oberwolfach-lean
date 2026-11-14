module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Host-density hypotheses imply the reference-family mass condition. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Oberwolfach

theorem marked_adaptive_reference_mass_from_host
    (n u:ℕ) (ρ₀ ρ D s₀ m pstar:ℝ)
    (hρ₀:0≤ρ₀) (hρ:ρ₀≤ρ) (hD:(n:ℝ)/2≤D)
    (hsize:ρ*D=2*u) (hs₀:0≤s₀) (hm:0<m)
    (hpstar:4*m*pstar≤ρ₀*s₀):
    pstar*n≤(s₀/m)*u := by
  have hρD:ρ₀*((n:ℝ)/2)≤ρ*D :=
    mul_le_mul hρ hD (by positivity) (hρ₀.trans hρ)
  have hmass:ρ₀*n≤4*(u:ℝ):=by nlinarith
  have hp:=mul_le_mul_of_nonneg_right hpstar (Nat.cast_nonneg n)
  have hu:=mul_le_mul_of_nonneg_right hmass hs₀
  have hh:m*(pstar*n)≤s₀*u:=by nlinarith
  have hi:(pstar*n)≤(s₀*(u:ℝ))/m:=(le_div_iff₀ hm).2 (by nlinarith only [hh])
  convert hi using 1 <;> ring
theorem marked_adaptive_host_index_lower
    (n u:ℕ) (ρ₀ ρ D ω:ℝ) (hρ₀:0≤ρ₀) (hρ:ρ₀≤ρ)
    (hD:(n:ℝ)/2≤D) (hsize:ρ*D=2*u) (hω:4*ω≤ρ₀):
    ω*n≤(u:ℝ) := by
  have hρD:ρ₀*((n:ℝ)/2)≤ρ*D :=
    mul_le_mul hρ hD (by positivity) (hρ₀.trans hρ)
  have hωn:=mul_le_mul_of_nonneg_right hω (Nat.cast_nonneg n)
  nlinarith
end Oberwolfach
