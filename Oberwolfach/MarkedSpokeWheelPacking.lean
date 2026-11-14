module

public import Oberwolfach.MarkedTransformerWheelPacking
public import Oberwolfach.HubCommonPathCycles

@[expose] public section

/-! Physical disjointness of spoke-wheel families, allowing repeated hubs
and repeated roots provided the actual old spoke pairs are distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    {H₀ HK:V→U→Prop}

 theorem marked_cycle_family_packing_no_old_arc
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedCycleTuple tail head ktail khead m π b) (R:Finset V) (P:I→Finset V)
    (hvertices:∀ i a,(C i).val a∈R∪P i)
    (hPP:∀ i j,i≠j→Disjoint (P i) (P j))
    (hroot:∀ i a,¬((C i).val a∈R∧(C i).val (finRotate (m+1) a)∈R)):
    ∀ i j,i≠j→Disjoint (markedCyclePhysicalEdges tail head ktail khead m π b (C i))
      (markedCyclePhysicalEdges tail head ktail khead m π b (C j)):=by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he
  obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hf
  have hc:=marked_cycle_common_physical_endpoints hp (C i) (C j) a z (ha.trans hz.symm)
  have common (x:V) (hx:x∈R∪P i) (hy:x∈R∪P j):x∈R:=by
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hx
    · rcases Finset.mem_union.mp hy with hy|hy
      · exact hy
      · exact (Finset.disjoint_left.mp (hPP i j hij) hx hy).elim
  exact hroot i a ⟨common _ (hvertices i a) (hc.1 ▸ hvertices j z),
    common _ (hvertices i _) (hc.2 ▸ hvertices j _)⟩

 theorem marked_spoke_wheel_family_packing
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W:I→MarkedWheel tail head ktail khead m π b H₀ HK) (R:Finset V) (P:I→Finset V)
    (v:I→V) (hold:Function.Injective (fun i=>(v i,(W i).2.val)))
    (hvertices:∀ i a,(W i).1.val a∈R∪P i)
    (hPP:∀ i j,i≠j→Disjoint (P i) (P j))
    (hroot:∀ i a,(W i).1.val a∈R→(W i).1.val a=v i)
    (hnoarc:∀ i a,¬((W i).1.val a∈R∧(W i).1.val (finRotate (m+1) a)∈R)):
    ∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W j)):=by
  have hr:=marked_cycle_family_packing_no_old_arc hp (fun i=>(W i).1) R P hvertices hPP hnoarc
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    exact Finset.disjoint_left.mp (hr i j hij) ((markedWheelPhysicalResources_rim _ _).mp he)
      ((markedWheelPhysicalResources_rim _ _).mp hf)
  | inr xu=>
    rw [markedWheelPhysicalResources_spoke] at he hf
    obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he.2
    obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hf.2
    have hx:xu.1∈R:=by
      have hx:=ha ▸ hvertices i a
      have hy:=hz ▸ hvertices j z
      rcases Finset.mem_union.mp hx with hx|hx
      · exact hx
      · rcases Finset.mem_union.mp hy with hy|hy
        · exact hy
        · exact (Finset.disjoint_left.mp (hPP i j hij) hx hy).elim
    have hv:v i=v j:=(hroot i a (ha ▸ hx)).symm.trans (ha.trans (hz.symm.trans (hroot j z (hz ▸ hx))))
    exact hij (hold (Prod.ext hv (he.1.trans hf.1.symm)))

end Oberwolfach
