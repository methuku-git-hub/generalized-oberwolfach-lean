module

public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.ResourceDecompositions
public import Oberwolfach.MarkedTransformerWheelPacking

@[expose] public section

/-! Attach a prescribed compatible hub to each cycle of a vertex-disjoint
marked factor, obtaining an exact physical wheel decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 def markedCycleResourcesAtHub (C:MarkedCycleTuple tail head ktail khead m π b) (u:U):Finset (Finset V⊕(V×U)):=
    (markedCyclePhysicalEdges tail head ktail khead m π b C).image Sum.inl∪
      (Finset.univ.image C.val).image (fun v=>Sum.inr (v,u))

 theorem markedCycleResourcesAtHub_rim (C:MarkedCycleTuple tail head ktail khead m π b) (u:U) (e:Finset V):
    Sum.inl e∈markedCycleResourcesAtHub C u↔e∈markedCyclePhysicalEdges tail head ktail khead m π b C:=by
  simp [markedCycleResourcesAtHub]

 theorem markedCycleResourcesAtHub_spoke (C:MarkedCycleTuple tail head ktail khead m π b) (u:U) (v:V) (z:U):
    Sum.inr (v,z)∈markedCycleResourcesAtHub C u↔z=u∧v∈Finset.univ.image C.val:=by
  simp only [markedCycleResourcesAtHub,Finset.mem_union,Finset.mem_image,
    Sum.inl_ne_inr,and_false,exists_false,false_or,Sum.inr.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨x,hx,rfl,hu⟩;exact ⟨hu.symm,hx⟩
  · rintro ⟨rfl,hv⟩;exact ⟨v,hv,rfl,rfl⟩

 theorem markedWheelPhysicalResources_eq_atHub {H₀ HK:V→U→Prop}
    (W:MarkedWheel tail head ktail khead m π b H₀ HK):
    markedWheelPhysicalResources W=markedCycleResourcesAtHub W.1 W.2.val:=by
  simp only [markedWheelPhysicalResources,markedCycleResourcesAtHub,Finset.image_image]
  rfl

 theorem marked_cycle_vertex_disjoint_physical
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C D:MarkedCycleTuple tail head ktail khead m π b)
    (hd:Disjoint (Finset.univ.image C.val) (Finset.univ.image D.val)):
    Disjoint (markedCyclePhysicalEdges tail head ktail khead m π b C)
      (markedCyclePhysicalEdges tail head ktail khead m π b D):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hf
  have hh:=(marked_cycle_common_physical_endpoints hp C D i j (hi.trans hj.symm)).1
  exact Finset.disjoint_left.mp hd (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hh.symm⟩)

 theorem marked_factor_at_hub_decomposition (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M:Finset (MarkedCycleTuple tail head ktail khead m π b)) (u:U)
    (hM:∀ C∈M,∀ D∈M,C≠D→Disjoint (Finset.univ.image C.val) (Finset.univ.image D.val))
    (hH:∀ C∈M,MarkedHubCompatible H₀ HK C.val u):
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
      (M.biUnion (fun C=>markedCycleResourcesAtHub C u)):=by
  apply resource_decomposition_biUnion _ (fun C=>markedCycleResourcesAtHub C u) M
  · intro C hC
    let W:MarkedWheel tail head ktail khead m π b H₀ HK:=⟨C,⟨u,hH C hC⟩⟩
    have hdec:=resource_decomposition_singleton markedWheelPhysicalResources W
    rw [markedWheelPhysicalResources_eq_atHub] at hdec
    exact hdec
  · intro C hC D hD hCD
    apply Finset.disjoint_left.mpr
    intro e he hf
    cases e with
    | inl e=>
      exact Finset.disjoint_left.mp (marked_cycle_vertex_disjoint_physical hp C D (hM C hC D hD hCD))
        ((markedCycleResourcesAtHub_rim C u e).mp he) ((markedCycleResourcesAtHub_rim D u e).mp hf)
    | inr vz=>
      exact Finset.disjoint_left.mp (hM C hC D hD hCD)
        ((markedCycleResourcesAtHub_spoke C u vz.1 vz.2).mp he).2
        ((markedCycleResourcesAtHub_spoke D u vz.1 vz.2).mp hf).2

 theorem marked_factor_at_hub_rim (M:Finset (MarkedCycleTuple tail head ktail khead m π b)) (u:U) (e:Finset V):
    Sum.inl e∈M.biUnion (fun C=>markedCycleResourcesAtHub C u)↔
      e∈M.biUnion (markedCyclePhysicalEdges tail head ktail khead m π b):=by
  simp only [Finset.mem_biUnion,markedCycleResourcesAtHub_rim]

 theorem marked_factor_at_hub_spoke (M:Finset (MarkedCycleTuple tail head ktail khead m π b)) (u:U) (v:V) (z:U):
    Sum.inr (v,z)∈M.biUnion (fun C=>markedCycleResourcesAtHub C u)↔
      z=u∧v∈M.biUnion (fun C=>Finset.univ.image C.val):=by
  simp only [Finset.mem_biUnion,markedCycleResourcesAtHub_spoke]
  tauto

end Oberwolfach
