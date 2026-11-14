module

public import Oberwolfach.LongReservedPathBlockGeometry
public import Oberwolfach.RegularCycleIsomorphism
public import Oberwolfach.CycleCopies

@[expose] public section
/-! A fixed cyclic ordering turns the arithmetic blocks into genuine,
vertex-disjoint extended paths in a two-factor component. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type*} [Fintype V] [DecidableEq V] (G:SimpleGraph V)
    (C:G.ConnectedComponent) [Fintype C]

def longReservedComponentBlock
    (e:SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (c d t i:ℕ) (ht:t≤d) (hfit:(c*d+5)*(i+1)≤Fintype.card C) : Fin (c*t+5) ↪ C where
  toFun j:=e ⟨(c*d+5)*i+j.val,by
    have hprod:c*t≤c*d:=Nat.mul_le_mul_left c ht
    simp only [Nat.mul_add,Nat.mul_one] at hfit
    omega⟩
  inj' := by
    intro x y hxy
    have hh:=e.injective hxy
    apply Fin.ext
    have hv:=congrArg Fin.val hh
    simp only at hv
    omega

theorem long_reserved_component_block_edges
    (e:SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (hthree:3≤Fintype.card C) (c d t i:ℕ) (ht:t≤d)
    (hfit:(c*d+5)*(i+1)≤Fintype.card C):
    ∀j:Fin (c*t+4),C.toSimpleGraph.Adj
      (longReservedComponentBlock G C e c d t i ht hfit ⟨j.val,by omega⟩)
      (longReservedComponentBlock G C e c d t i ht hfit ⟨j.val+1,by omega⟩) := by
  intro j
  apply e.map_rel_iff.mpr
  apply (cycleGraph_modular_adj (by omega) _ _).2
  left
  apply Nat.mod_eq_of_lt
  have hprod:c*t≤c*d:=Nat.mul_le_mul_left c ht
  simp only [Nat.mul_add,Nat.mul_one] at hfit
  change (c*d+5)*i+j.val+1 < Fintype.card C
  omega

theorem long_reserved_component_blocks_disjoint
    (e:SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (c d t t' i j:ℕ) (ht:t≤d) (ht':t'≤d)
    (hi:(c*d+5)*(i+1)≤Fintype.card C) (hj:(c*d+5)*(j+1)≤Fintype.card C) (hij:i≠j):
    Disjoint (Finset.univ.image (longReservedComponentBlock G C e c d t i ht hi))
      (Finset.univ.image (longReservedComponentBlock G C e c d t' j ht' hj)) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hxi
  obtain ⟨b,_,hb⟩:=Finset.mem_image.mp hxj
  have heq:=e.injective (ha.trans hb.symm)
  have hv:=congrArg Fin.val heq
  have haMem:(c*d+5)*i+a.val∈longReservedExtendedBlock c d t i:=by
    simp only [longReservedExtendedBlock,Finset.mem_Icc]
    omega
  have hbMem:(c*d+5)*j+b.val∈longReservedExtendedBlock c d t' j:=by
    simp only [longReservedExtendedBlock,Finset.mem_Icc]
    omega
  have hdis:=long_reserved_extended_blocks_disjoint c d t t' i j ht ht' hij
  have hval:(c*d+5)*i+a.val=(c*d+5)*j+b.val:=by simpa [longReservedComponentBlock] using hv
  exact (Finset.disjoint_left.mp hdis) haMem (hval ▸ hbMem)
end Oberwolfach
