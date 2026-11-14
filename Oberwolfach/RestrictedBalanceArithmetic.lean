module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Deterministic error arithmetic for the three restricted marked
vertex balances and the hub type ratio. -/
set_option autoImplicit false
namespace Oberwolfach

theorem degree_centre_transfer (x p D d e δ : ℝ) (hp : 0≤p)
    (hx : |x-p*d|≤e) (hd : |d-D|≤δ) : |x-p*D|≤e+p*δ := by
  have he : x-p*D=(x-p*d)+p*(d-D) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add hx
  rw [abs_mul,abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left hd hp

theorem restricted_vertex_balance_error (r0 rK h0 hK p k s t D B ε L δ : ℝ)
    (hD0 : p*D=s*B) (hDK : k*D=t*B)
    (hr0 : |r0-p*D|≤ε+L+p*δ) (hrK : |rK-k*D|≤ε+L+k*δ)
    (hh0 : |h0-s*B|≤ε) (hhK : |hK-t*B|≤ε) :
    |r0+rK-(h0+hK)|≤4*ε+2*L+(p+k)*δ := by
  have he : r0+rK-(h0+hK)=((r0-p*D)+(rK-k*D))-((h0-s*B)+(hK-t*B)) := by
    rw [hD0,hDK]
    ring
  rw [he]
  have hfirst := abs_sub_le ((r0-p*D)+(rK-k*D)) 0 ((h0-s*B)+(hK-t*B))
  simp only [sub_zero,zero_sub,abs_neg] at hfirst
  have hr := abs_add_le (r0-p*D) (rK-k*D)
  have hh := abs_add_le (h0-s*B) (hK-t*B)
  nlinarith only [hfirst,hr,hh,hr0,hrK,hh0,hhK]

theorem restricted_marked_balance_error (r h k t D B ε L δ : ℝ)
    (hDK : k*D=t*B) (hr : |r-k*D|≤ε+L+k*δ) (hh : |h-t*B|≤ε) :
    |r-h|≤2*ε+L+k*δ := by
  have he := abs_sub_le r (k*D) h
  rw [abs_sub_comm (k*D),hDK] at he
  rw [hDK] at hr
  linarith only [he,hr,hh]

theorem restricted_hub_balance_error (h0 hK s t A ε m : ℝ)
    (hm : 0≤m) (hs : s=m*t) (hh0 : |h0-s*A|≤ε) (hhK : |hK-t*A|≤ε) :
    |h0-m*hK|≤(1+m)*ε := by
  have he : h0-m*hK=(h0-s*A)-m*(hK-t*A) := by rw [hs];ring
  rw [he]
  have hh := abs_sub_le (h0-s*A) 0 (m*(hK-t*A))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hm] at hh
  have hmul := mul_le_mul_of_nonneg_left hhK hm
  nlinarith only [hh,hmul,hh0]

end Oberwolfach
