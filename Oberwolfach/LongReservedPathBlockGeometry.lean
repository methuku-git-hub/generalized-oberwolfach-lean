module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Arithmetic geometry of the two-edge extensions of reserved paths
inside the manuscript's blocks of length c*d+5. -/
set_option autoImplicit false
namespace Oberwolfach

def longReservedExtendedBlock (c d t i:ℕ) : Finset ℕ :=
  Finset.Icc ((c*d+5)*i) ((c*d+5)*i+c*t+4)

def longReservedFullBlock (c d i:ℕ) : Finset ℕ :=
  Finset.Ico ((c*d+5)*i) ((c*d+5)*(i+1))

theorem long_reserved_extended_block_subset
    (c d t i:ℕ) (ht:t≤d):
    longReservedExtendedBlock c d t i ⊆ longReservedFullBlock c d i := by
  intro x hx
  have hprod:c*t≤c*d:=Nat.mul_le_mul_left c ht
  simp only [longReservedExtendedBlock,Finset.mem_Icc] at hx
  simp only [longReservedFullBlock,Finset.mem_Ico,Nat.mul_add,Nat.mul_one]
  omega

theorem long_reserved_full_blocks_disjoint
    (c d i j:ℕ) (hij:i≠j):
    Disjoint (longReservedFullBlock c d i) (longReservedFullBlock c d j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  simp only [longReservedFullBlock,Finset.mem_Ico] at hxi hxj
  rcases lt_or_gt_of_ne hij with hij|hji
  · have hbase: (c*d+5)*(i+1)≤(c*d+5)*j:=Nat.mul_le_mul_left _ (by omega)
    omega
  · have hbase: (c*d+5)*(j+1)≤(c*d+5)*i:=Nat.mul_le_mul_left _ (by omega)
    omega

theorem long_reserved_extended_blocks_disjoint
    (c d t t' i j:ℕ) (ht:t≤d) (ht':t'≤d) (hij:i≠j):
    Disjoint (longReservedExtendedBlock c d t i) (longReservedExtendedBlock c d t' j) :=
  (long_reserved_full_blocks_disjoint c d i j hij).mono
    (long_reserved_extended_block_subset c d t i ht)
    (long_reserved_extended_block_subset c d t' j ht')

theorem long_reserved_path_length_in_block (c d t i:ℕ):
    ((c*d+5)*i+2+c*t)-((c*d+5)*i+2)=c*t := by omega
end Oberwolfach
