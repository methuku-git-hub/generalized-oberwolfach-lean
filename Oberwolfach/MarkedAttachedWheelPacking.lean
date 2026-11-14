module

public import Oberwolfach.MarkedAttachmentWheelFamilies
public import Oberwolfach.MarkedCrossFamilyPacking
public import Oberwolfach.MarkedRootGraphSupport
public import Oberwolfach.ResourceFamilyIndicators

@[expose] public section

/-! Wheels with a single old row have no old rim edge. Distinct fresh hubs
then make the entire attached family a physical packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

theorem marked_one_old_position_no_old_arc (hm:0<m)
    (C:MarkedCycleTuple tail head ktail khead m π b) (k:Fin (m+1))
    (Z:Finset V) (hnew:∀ t,t≠k→C.val t∉Z):
    ∀ t,¬(C.val t∈Z∧C.val (finRotate (m+1) t)∈Z):=by
  intro t ht
  have ht₀:t=k:=by by_contra h;exact hnew t h ht.1
  have ht₁:finRotate (m+1) t=k:=by by_contra h;exact hnew _ h ht.2
  exact finRotate_ne_self_of_pos hm t (ht₀.trans ht₁.symm)

theorem marked_wheel_without_old_resources
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:MarkedWheel tail head ktail khead m π b H₀ HK) (Z:Finset V) (B:Finset U)
    (hnoarc:∀ k,¬(C.1.val k∈Z∧C.1.val (finRotate (m+1) k)∈Z)) (hB:C.2.val∉B):
    ∀ e∈markedWheelPhysicalResources C,¬MarkedOldResource tail head ktail khead π Z B e:=by
  intro e he hold
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩:=hold
    obtain ⟨k,_,hk⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim C e).mp he)
    have hka:=hp (hk.trans ha.symm)
    have ends:=markedCycleTypedEdge_endpoints tail head ktail khead m π b C.1 k
    rw [hka] at ends
    exact hnoarc k ⟨ends.1 ▸ hat,ends.2 ▸ hah⟩
  | inr vu=>
    have hh:=((markedWheelPhysicalResources_spoke C vu.1 vu.2).mp he).1
    exact hB (hh.symm ▸ hold.2)

theorem marked_attached_wheels_pack
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (hm:0<m)
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK) (k:I→Fin (m+1))
    (Z:Finset V) (hroot:∀ i,(C i).1.val (k i)∈Z)
    (hnew:∀ i t,t≠k i→(C i).1.val t∉Z)
    (hhub:Function.Injective (fun i=>(C i).2.val))
    (hdis:∀ i j,i≠j→Disjoint ((Finset.univ.filter (·≠k i)).image (C i).1.val)
      ((Finset.univ.filter (·≠k j)).image (C j).1.val)):
    ∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)):=by
  intro i j hij
  apply marked_wheels_disjoint_of_shared_labels hp (C i) (C j) Z ?_
    (marked_one_old_position_no_old_arc hm (C j).1 (k j) Z (hnew j))
    (fun _ _ _ he=>hij (hhub he))
  intro t t' he
  by_cases ht:t=k i
  · subst t;exact he ▸ hroot i
  by_cases ht':t'=k j
  · subst t';exact hroot j
  exact False.elim (Finset.disjoint_left.mp (hdis i j hij)
    (Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,rfl⟩)
    (Finset.mem_image.mpr ⟨t',Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht'⟩,he.symm⟩))

theorem marked_attached_wheel_disjoint_old_graph {A S:Type} [Fintype A] [Fintype S]
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (hm:0<m)
    (C:MarkedWheel tail head ktail khead m π b H₀ HK) (k:Fin (m+1)) (Z:Finset V) (B:Finset U)
    (hnew:∀ t,t≠k→C.1.val t∉Z) (hB:C.2.val∉B)
    (src dst:A→V) (row:S→V) (jr:A→Bool) (hub:S→U)
    (hr:∀ a,src a∈Z∧dst a∈Z) (hs:∀ s,row s∈Z∧hub s∈B)
    (ha:∀ a,if jr a then ∃ e,ktail e=src a∧khead e=dst a else ∃ e,tail e=src a∧head e=dst a):
    Disjoint (markedWheelPhysicalResources C) (markedRootGraphResources π src dst row jr hub):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact marked_wheel_without_old_resources hp C Z B
    (marked_one_old_position_no_old_arc hm C.1 k Z hnew) hB e he
    (marked_root_graph_old_supported src dst row jr hub Z B hr hs ha e hf).1

end Oberwolfach
