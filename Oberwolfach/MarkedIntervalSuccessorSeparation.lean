module

public import Oberwolfach.MarkedPermutationIntervalGeometry

@[expose] public section
/-! Successors of marked roots are roots or final interval endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_interval_successor_subset
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V):
    (markedIntervalRootSet π k a).image π⊆
      markedIntervalRootSet π k a ∪ Finset.univ.image (fun j=>(π^(k j)) (a j)):=by
  classical
  intro x hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hy
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
  have hp:π ((π^i.val) (a j))=(π^(i.val+1)) (a j):=by
    rw [pow_succ',Equiv.Perm.mul_apply]
  rw [hp]
  by_cases hi:i.val+1<k j
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨⟨i.val+1,hi⟩,Finset.mem_univ _,rfl⟩⟩
  · apply Finset.mem_union_right
    have he:i.val+1=k j:=by omega
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by rw [he]⟩

theorem marked_residual_ordinary_avoids_successors
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V) (Z R:Finset V)
    (hR:R=Finset.univ\(Z ∪ Finset.univ.image (fun j=>(π^(k j)) (a j)))):
    Disjoint (R\markedIntervalRootSet π k a) ((markedIntervalRootSet π k a).image π):=by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hsucc:=marked_interval_successor_subset π k a hy
  rcases Finset.mem_union.mp hsucc with hroot | hend
  · exact (Finset.mem_sdiff.mp hx).2 hroot
  · have hxR: x∈R:=(Finset.mem_sdiff.mp hx).1
    rw [hR] at hxR
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_union_right _ hend)
end Oberwolfach
