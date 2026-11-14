module

public import Oberwolfach.LongReservedBlockAllocation

@[expose] public section
/-! A floor-free sufficient capacity estimate for the reserved blocks. -/
set_option autoImplicit false
open scoped BigOperators
namespace Oberwolfach

theorem long_reserved_block_floor_lower
    (L h:ℕ) (hL:0<L) (hlarge:L≤h):
    h≤2*L*(h/L) := by
  have hq:1≤h/L:=(Nat.le_div_iff_mul_le hL).2 (by simpa using hlarge)
  have hqL:L≤L*(h/L):=by
    simpa using Nat.mul_le_mul_left L hq
  have hmod:h%L<L:=Nat.mod_lt h hL
  have hsum:=Nat.mod_add_div h L
  nlinarith

theorem long_reserved_total_block_capacity
    {I:Type*} [Fintype I] (L:ℕ) (hL:0<L) (length:I→ℕ)
    (hlarge:∀i,L≤length i) (requests:ℕ)
    (hrequested:2*L*requests≤∑i,length i):
    requests≤∑i,length i/L := by
  have hsum:(∑i,length i)≤∑i,2*L*(length i/L):=by
    apply Finset.sum_le_sum
    intro i hi
    exact long_reserved_block_floor_lower L (length i) hL (hlarge i)
  rw [← Finset.mul_sum] at hsum
  have hp:0<2*L:=by omega
  exact Nat.le_of_mul_le_mul_left (hrequested.trans hsum) hp
end Oberwolfach
