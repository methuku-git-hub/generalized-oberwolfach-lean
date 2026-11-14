module

public import Oberwolfach.MarkedWheelResources

@[expose] public section

/-! Disjointness of actual physical resources follows from the injective
host map, private path vertices and the old root edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    {H₀ HK:V→U→Prop}

 theorem marked_cycle_common_physical_endpoints
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C D:MarkedCycleTuple tail head ktail khead m π b) (i j:Fin (m+1))
    (he:markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C i)=
      markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b D j)):
    C.val i=D.val j∧C.val (finRotate (m+1) i)=D.val (finRotate (m+1) j):=by
  have ht:=hp he
  have hC:=markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  have hD:=markedCycleTypedEdge_endpoints tail head ktail khead m π b D j
  exact ⟨hC.1.symm.trans ((congrArg (Sum.elim tail ktail) ht).trans hD.1),
    hC.2.symm.trans ((congrArg (Sum.elim head khead) ht).trans hD.2)⟩

 theorem private_path_common_vertex (R A B:Finset V) (hAR:Disjoint A R)
    (hBR:Disjoint B R) (hAB:Disjoint A B) (x:V) (hx:x∈R∪A) (hy:x∈R∪B):x∈R:=by
  rcases Finset.mem_union.mp hx with hx|hx
  · exact hx
  · rcases Finset.mem_union.mp hy with hy|hy
    · exact hy
    · exact (Finset.disjoint_left.mp hAB hx hy).elim

 theorem marked_rim_cycle_family_packing
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedCycleTuple tail head ktail khead m π b) (R:Finset V) (P:I→Finset V)
    (old:I→Finset V) (hold:Function.Injective old)
    (hvertices:∀ i a,(C i).val a∈R∪P i)
    (hPR:∀ i,Disjoint (P i) R) (hPP:∀ i j,i≠j→Disjoint (P i) (P j))
    (hroot:∀ i a,(C i).val a∈R→(C i).val (finRotate (m+1) a)∈R→
      markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b (C i) a)=old i):
    ∀ i j,i≠j→Disjoint (markedCyclePhysicalEdges tail head ktail khead m π b (C i))
      (markedCyclePhysicalEdges tail head ktail khead m π b (C j)):=by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he
  obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hf
  have hc:=marked_cycle_common_physical_endpoints hp (C i) (C j) a z (ha.trans hz.symm)
  have htail:(C i).val a∈R:=private_path_common_vertex R (P i) (P j) (hPR i) (hPR j) (hPP i j hij) _
    (hvertices i a) (hc.1 ▸ hvertices j z)
  have hhead:(C i).val (finRotate (m+1) a)∈R:=private_path_common_vertex R (P i) (P j)
    (hPR i) (hPR j) (hPP i j hij) _ (hvertices i _) (hc.2 ▸ hvertices j _)
  have htail':(C j).val z∈R:=hc.1 ▸ htail
  have hhead':(C j).val (finRotate (m+1) z)∈R:=hc.2 ▸ hhead
  exact hij (hold ((hroot i a htail hhead).symm.trans ((ha.trans hz.symm).trans (hroot j z htail' hhead'))))

 theorem marked_wheel_packing_of_distinct_hubs
    (W:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hh:Function.Injective (fun i=>(W i).2.val))
    (hr:∀ i j,i≠j→Disjoint (markedCyclePhysicalEdges tail head ktail khead m π b (W i).1)
      (markedCyclePhysicalEdges tail head ktail khead m π b (W j).1)):
    ∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W j)):=by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    exact Finset.disjoint_left.mp (hr i j hij) ((markedWheelPhysicalResources_rim _ _).mp he)
      ((markedWheelPhysicalResources_rim _ _).mp hf)
  | inr vu=>
    rw [markedWheelPhysicalResources_spoke] at he hf
    exact hij (hh (he.1.trans hf.1.symm))

end Oberwolfach
