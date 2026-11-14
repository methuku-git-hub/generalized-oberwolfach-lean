module

public import Oberwolfach.MarkedSpokeWheelPacking
public import Oberwolfach.MarkedRootArcIsolation
public import Oberwolfach.SharedTwoRootCycleGeometry

@[expose] public section

/-! Apply physical packing to the actual path-based wheels. The root arc
or root spoke is the only possible resource shared through old labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_actual_rim_wheel_packing (n:ℕ) (hn:2≤n)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:I→(Fin (n+1)→V)) (v w:I→V) (j:I→Bool) (R:Finset V)
    (W:I→MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hW:∀ i a,(W i).1.val a=Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (p i))
      (canonicalMarkedRotation (if j i then 0 else 3) a))
    (hroot:∀ i,v i∈R∧w i∈R) (hfree:∀ i a,p i a∉R)
    (hdis:∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))
    (hhub:Function.Injective (fun i=>(W i).2.val))
    (hold:Function.Injective (fun i=>if j i then ({v i,π (w i)}:Finset V) else {v i,w i})):
    ∀ i k,i≠k→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W k)):=by
  apply marked_wheel_packing_of_distinct_hubs W hhub
  apply marked_rim_cycle_family_packing hp (fun i=>(W i).1) R (fun i=>Finset.univ.image (p i)) _ hold
  · intro i a
    have hval:(W i).1.val=fun a=>Fin.cons (α:=fun _=>V) (v i) (Fin.cons (w i) (p i))
        (canonicalMarkedRotation (if j i then 0 else 3) a):=funext (hW i)
    have hm:(W i).1.val a∈Finset.univ.image (W i).1.val:=Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    have himage:Finset.univ.image (W i).1.val=insert (v i) (insert (w i) (Finset.univ.image (p i))):=by
      rw [hval,two_root_cycle_image]
    rw [himage] at hm
    rcases Finset.mem_insert.mp hm with hm|hm
    · exact Finset.mem_union_left _ (hm ▸ (hroot i).1)
    · rcases Finset.mem_insert.mp hm with hm|hm
      · exact Finset.mem_union_left _ (hm ▸ (hroot i).2)
      · exact Finset.mem_union_right _ hm
  · intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hx
    exact hfree i a hxR
  · exact hdis
  · intro i a ht hh
    exact marked_two_root_wheel_old_arc n hn (p i) (v i) (w i) (j i) R (hfree i) (W i) (hW i) a ht hh

 theorem marked_actual_spoke_wheel_packing (n:ℕ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:I→(Fin (n+1)→V)) (v:I→V) (j:I→Bool) (R:Finset V)
    (W:I→MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hW:∀ i a,(W i).1.val a=rootedCycleOrder (markedRootOrder (n+1) (j i)) (v i) (p i) a)
    (hroot:∀ i,v i∈R) (hfree:∀ i a,p i a∉R)
    (hdis:∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))
    (hold:Function.Injective (fun i=>(v i,(W i).2.val))):
    ∀ i k,i≠k→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W k)):=by
  have hv (i:I) (a:Fin (n+2)):(W i).1.val a=v i∨(W i).1.val a∈Finset.univ.image (p i):=by
    have hval:(W i).1.val=rootedCycleOrder (markedRootOrder (n+1) (j i)) (v i) (p i):=funext (hW i)
    have hm:(W i).1.val a∈Finset.univ.image (W i).1.val:=Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    rw [hval,rootedCycleOrder_vertices] at hm
    rw [← hW i a] at hm
    exact Finset.mem_insert.mp hm
  apply marked_spoke_wheel_family_packing hp W R (fun i=>Finset.univ.image (p i)) v hold
  · intro i a
    rcases hv i a with he|he
    · exact Finset.mem_union_left _ (he ▸ hroot i)
    · exact Finset.mem_union_right _ he
  · exact hdis
  · intro i a ha
    rcases hv i a with he|he
    · exact he
    · obtain ⟨z,_,hz⟩:=Finset.mem_image.mp he
      exact (hfree i z (hz ▸ ha)).elim
  · intro i
    exact marked_one_root_wheel_no_old_arc (p i) (v i) R (hfree i)
      (markedRootOrder (n+1) (j i)) (markedRootOrder_successor (n+1) (j i)) (W i) (hW i)

end Oberwolfach
