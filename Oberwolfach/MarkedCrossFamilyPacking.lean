module

public import Oberwolfach.MarkedActualWheelPacking

@[expose] public section

/-! Physical disjointness across the rim-wheel and spoke-wheel families.
Shared physical edges are pulled back to their original directed endpoints;
no identification of a marked head with its physical successor is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_cycles_disjoint_of_shared_labels
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C D:MarkedCycleTuple tail head ktail khead m π b) (S:Finset V)
    (hshared:∀ i j,C.val i=D.val j→D.val j∈S)
    (hnoarc:∀ j,¬(D.val j∈S∧D.val (finRotate (m+1) j)∈S)):
    Disjoint (markedCyclePhysicalEdges tail head ktail khead m π b C)
      (markedCyclePhysicalEdges tail head ktail khead m π b D):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hf
  have hc:=marked_cycle_common_physical_endpoints hp C D i j (hi.trans hj.symm)
  exact hnoarc j ⟨hshared i j hc.1,hshared _ _ hc.2⟩

 theorem marked_wheels_disjoint_of_shared_labels
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C D:MarkedWheel tail head ktail khead m π b H₀ HK) (S:Finset V)
    (hshared:∀ i j,C.1.val i=D.1.val j→D.1.val j∈S)
    (hnoarc:∀ j,¬(D.1.val j∈S∧D.1.val (finRotate (m+1) j)∈S))
    (hspoke:∀ i j,C.1.val i=D.1.val j→C.2.val≠D.2.val):
    Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources D):=by
  have hr:=marked_cycles_disjoint_of_shared_labels hp C.1 D.1 S hshared hnoarc
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    exact Finset.disjoint_left.mp hr ((markedWheelPhysicalResources_rim C e).mp he)
      ((markedWheelPhysicalResources_rim D e).mp hf)
  | inr vu=>
    rw [markedWheelPhysicalResources_spoke] at he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he.2
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hf.2
    exact hspoke i j (hi.trans hj.symm) (he.1.trans hf.1.symm)

 theorem marked_rim_spoke_cross_packing (n:ℕ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:Fin (n+1)→V) (v w:V) (jr:Bool) (q:Fin (n+2)→V) (x:V) (js:Bool)
    (R:Finset V) (C D:MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hC:∀ i,C.1.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p)
      (canonicalMarkedRotation (if jr then 0 else 3) i))
    (hD:∀ i,D.1.val i=rootedCycleOrder (markedRootOrder (n+2) js) x q i)
    (hv:v∈R) (hw:w∈R) (hx:x∈R)
    (hq:∀ i,q i∉R) (hdis:Disjoint (Finset.univ.image p) (Finset.univ.image q))
    (hhub:C.2.val≠D.2.val):
    Disjoint (markedWheelPhysicalResources C) (markedWheelPhysicalResources D):=by
  have hCs:∀ i,C.1.val i∈R∪Finset.univ.image p:=by
    intro i
    have hi:C.1.val i∈Finset.univ.image C.1.val:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have him:Finset.univ.image C.1.val=insert v (insert w (Finset.univ.image p)):=by
      rw [funext hC,two_root_cycle_image]
    rw [him] at hi
    rcases Finset.mem_insert.mp hi with hi|hi
    · exact Finset.mem_union_left _ (hi ▸ hv)
    · rcases Finset.mem_insert.mp hi with hi|hi
      · exact Finset.mem_union_left _ (hi ▸ hw)
      · exact Finset.mem_union_right _ hi
  have hDs:∀ i,D.1.val i∈R∪Finset.univ.image q:=by
    intro i
    have hi:D.1.val i∈Finset.univ.image D.1.val:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [funext hD,rootedCycleOrder_vertices] at hi
    rw [←hD i] at hi
    rcases Finset.mem_insert.mp hi with hi|hi
    · exact Finset.mem_union_left _ (hi ▸ hx)
    · exact Finset.mem_union_right _ hi
  apply marked_wheels_disjoint_of_shared_labels hp C D R ?_
    (marked_one_root_wheel_no_old_arc q x R hq (markedRootOrder (n+2) js)
      (markedRootOrder_successor (n+2) js) D hD) (fun _ _ _=>hhub)
  intro i j hij
  have h1:=hij ▸ hCs i
  have h2:=hDs j
  rcases Finset.mem_union.mp h1 with h1|h1
  · exact h1
  · rcases Finset.mem_union.mp h2 with h2|h2
    · exact h2
    · exact False.elim (Finset.disjoint_left.mp hdis h1 h2)

end Oberwolfach
