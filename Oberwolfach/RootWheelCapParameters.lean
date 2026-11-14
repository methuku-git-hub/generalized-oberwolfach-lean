module

public import Oberwolfach.CappedRootWheelPacking

@[expose] public section

/-! Choose a fixed internal-use cap before the order and forbidden degree.
The scalar conclusion supplies the exact margin used by the physical
root-wheel construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach

theorem root_wheel_cap_parameters (r:ℕ) (C β:ℝ) (hC:0≤C) (hβ:0<β) :
    ∃ K:ℕ,0<K ∧ ∃ ζ:ℝ,0<ζ ∧ ∃ n₀:ℕ,∀ n N:ℕ,n₀≤n →
      (N:ℝ)≤C*n → ∀ L:ℝ,0≤L → L≤ζ*n →
      (N*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(L+1)+4*(K+1)<β*n := by
  obtain ⟨K₀,hK₀⟩:=exists_nat_gt (4*C*r/β)
  let K:=K₀+1
  have hK:0<K:=by dsimp [K];omega
  have hKR:(0:ℝ)<K:=Nat.cast_pos.mpr hK
  have hKmargin:4*C*r<β*K:=by
    have hh:4*C*r/β<(K:ℝ):=hK₀.trans_le (by dsimp [K];push_cast;linarith)
    have hh':=(div_lt_iff₀ hβ).mp hh
    nlinarith only [hh']
  let ζ:=β/(4*((r:ℝ)+3))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  obtain ⟨n₀,hn₀⟩:=exists_nat_gt (2*(((r:ℝ)+3)+4*(K+1))/β)
  refine ⟨K,hK,ζ,hζ,n₀,?_⟩
  intro n N hn hN L hL hLsmall
  have hnR:(n₀:ℝ)≤n:=Nat.cast_le.mpr hn
  have hconstant:2*(((r:ℝ)+3)+4*(K+1))<β*n:=by
    have hh:=(div_lt_iff₀ hβ).mp (hn₀.trans_le hnR)
    nlinarith only [hh]
  have hnpos:(0:ℝ)<n:=by
    have hh : 0<β*n:=lt_trans (by positivity) hconstant
    exact (mul_pos_iff.mp hh).resolve_right (fun h=>not_lt_of_ge hβ.le h.1) |>.2
  have hterm:(N*r:ℕ)/(K:ℝ)≤β*n/4:=by
    apply (div_le_iff₀ hKR).mpr
    push_cast
    have hh:=mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg r)
    have hk':=mul_le_mul_of_nonneg_right hKmargin.le hnpos.le
    nlinarith only [hh,hk']
  have hLterm:((r:ℝ)+3)*L≤β*n/4:=by
    have hh:=mul_le_mul_of_nonneg_left hLsmall (show (0:ℝ)≤r+3 by positivity)
    have he:((r:ℝ)+3)*(ζ*n)=β*n/4:=by dsimp [ζ];field_simp
    rwa [he] at hh
  nlinarith only [hterm,hLterm,hconstant]

end Oberwolfach
