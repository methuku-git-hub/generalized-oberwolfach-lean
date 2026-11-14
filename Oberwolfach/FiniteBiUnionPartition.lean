module

public import Oberwolfach.WalkPhysicalEdgeUnion

@[expose] public section
/-! Partition a disjoint family of edge sets by a partition of their indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_biUnion_partition
    {I R E:Type*} [Fintype I] [Fintype R] (blocks:I→Finset R) (edges:R→Finset E)
    (hcover:Finset.univ.biUnion blocks=Finset.univ)
    (hblocks:∀i j:I,i≠j→Disjoint (blocks i) (blocks j))
    (hedges:∀r s:R,r≠s→Disjoint (edges r) (edges s)):
    (∀i j:I,i≠j→Disjoint ((blocks i).biUnion edges) ((blocks j).biUnion edges)) ∧
    Finset.univ.biUnion (fun i=>(blocks i).biUnion edges)=Finset.univ.biUnion edges := by
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨r,hri,hxr⟩:=Finset.mem_biUnion.mp hxi
    obtain ⟨s,hsj,hxs⟩:=Finset.mem_biUnion.mp hxj
    have hrs:r≠s:=by
      intro h
      subst s
      exact Finset.disjoint_left.mp (hblocks i j hij) hri hsj
    exact Finset.disjoint_left.mp (hedges r s hrs) hxr hxs
  · ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,r,hr,hx⟩
      exact ⟨r,hx⟩
    · rintro ⟨r,hx⟩
      have hr:r∈Finset.univ.biUnion blocks:=by rw [hcover];exact Finset.mem_univ r
      obtain ⟨i,_,hri⟩:=Finset.mem_biUnion.mp hr
      exact ⟨i,r,hri,hx⟩
end Oberwolfach
