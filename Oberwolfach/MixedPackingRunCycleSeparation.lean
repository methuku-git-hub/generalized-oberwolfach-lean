module

public import Oberwolfach.MixedPackingSpokeSeparation

@[expose] public section
/-! The actual marked-run images and the ordinary rim images in one mixed
packing have disjoint vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_packed_run_avoids_ordinary_rim
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (tail head:E→V) (ktail khead:L→V) (m b n:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop) (root:K→V)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (C:OrderedOrdinaryWheel (U:=U) π b n)
    (hhub:∀z,C.2=(W z).2.val)
    (hpack:∀z,Disjoint (ordinaryWheelPhysicalResources C) (markedWheelPhysicalResources (W z)))
    (Ord:Finset V) (hOrd:∀i,C.1.val i∈Ord)
    (havoid:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord)
    (r:SelectedRunIndex data.s₂ data.d data.T)
    (q:(SimpleGraph.completeGraph V).Walk ((π^r.2.val.1) (root r.1.val)) ((π^(r.2.val.2+1)) (root r.1.val)))
    (hq:∀x,x∈q.support→x=(π^(r.2.val.2+1)) (root r.1.val) ∨
      ∃z:actualSelectedSegmentIndex data,z.1=r ∧ ∃j:Fin (m+1),(W z).1.val j=x):
    Disjoint (Finset.univ.image C.1.val) q.support.toFinset:=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hx
  rcases hq x (List.mem_toFinset.mp hy) with he|⟨z,_,j,hj⟩
  · have hm:(π^(r.2.val.2+1)) (root r.1.val)∈permutationWindow π 0 data.d (root r.1.val):=by
      rw [permutationWindow_mem_iff]
      simp only [zero_add,pow_zero,Equiv.refl_apply]
      exact ⟨⟨r.2.val.2+1,by have hh:=(actual_selected_run_bounds data r).2;omega⟩,rfl⟩
    have ho:(π^(r.2.val.2+1)) (root r.1.val)∈Ord:=by rw [←he,←hi];exact hOrd i
    exact Finset.disjoint_left.mp (havoid r.1.val) hm ho
  · exact ordinary_marked_packing_spokes_distinct C (W z) (hhub z) (hpack z) i j (hi.trans hj.symm)

theorem ordinary_packed_rims_disjoint
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    {π:Equiv.Perm V} {b n k:ℕ}
    (C:OrderedOrdinaryWheel (U:=U) π b n) (D:OrderedOrdinaryWheel (U:=U) π b k)
    (hhub:C.2=D.2)
    (hdis:Disjoint (ordinaryWheelPhysicalResources C) (ordinaryWheelPhysicalResources D)):
    Disjoint (Finset.univ.image C.1.val) (Finset.univ.image D.1.val):=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hx
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hy
  exact ordinary_packing_spokes_distinct C D hhub hdis i j (hi.trans hj.symm)
end Oberwolfach
