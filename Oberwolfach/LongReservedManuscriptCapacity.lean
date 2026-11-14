module

public import Oberwolfach.LongReservedBlockCapacity

@[expose] public section
/-! The numerical sufficient condition stated after the reserved-path lemma. -/
set_option autoImplicit false
open scoped BigOperators
namespace Oberwolfach

theorem long_reserved_manuscript_capacity
    {I:Type*} [Fintype I] (L n K requests:ℕ) (length:I→ℕ) (η:ℝ)
    (hL:0<L) (hη:0<η) (hη1:η≤1)
    (hK:2*(L:ℝ)/η≤K) (hlength:∀i,(K:ℝ)≤length i)
    (hsum:η*n≤∑i:I,(length i:ℝ))
    (hrequests:(requests:ℝ)≤η*n/(2*(L:ℝ))):
    requests≤∑i:I,length i/L := by
  have hK' : 2*(L:ℝ)≤η*(K:ℝ):=by simpa [mul_comm] using (div_le_iff₀ hη).mp hK
  have hKnonneg:0≤(K:ℝ):=by positivity
  have hlarge:∀i,L≤length i:=by
    intro i
    have hh:0≤(1-η)*(K:ℝ):=mul_nonneg (by linarith) hKnonneg
    have hreal:(L:ℝ)≤length i:=by have hi:=hlength i;nlinarith
    exact_mod_cast hreal
  have hden:0<2*(L:ℝ):=by exact_mod_cast (show 0<2*L by omega)
  have hreq:2*L*requests≤∑i:I,length i:=by
    have hh:((2:ℝ)*(L:ℝ))*(requests:ℝ)≤η*n:=by simpa [mul_comm] using (le_div_iff₀ hden).mp hrequests
    have hreal:((2*L*requests:ℕ):ℝ)≤∑i:I,(length i:ℝ):=by push_cast;nlinarith
    exact_mod_cast hreal
  exact long_reserved_total_block_capacity L hL length hlarge requests hreq
theorem long_reserved_manuscript_floor_capacity
    {I:Type*} [Fintype I] (L n K requests:ℕ) (length:I→ℕ) (η:ℝ)
    (hL:0<L) (hη:0<η) (hη1:η≤1)
    (hK:2*(L:ℝ)/η≤K) (hlength:∀i,(K:ℝ)≤length i)
    (hsum:η*n≤∑i:I,(length i:ℝ))
    (hrequests:requests≤⌊η*n/(2*(L:ℝ))⌋₊):
    requests≤∑i:I,length i/L := by
  have hnonneg:0≤η*n/(2*(L:ℝ)):=by positivity
  exact long_reserved_manuscript_capacity L n K requests length η hL hη hη1 hK hlength hsum
    ((Nat.le_floor_iff hnonneg).mp hrequests)
end Oberwolfach
