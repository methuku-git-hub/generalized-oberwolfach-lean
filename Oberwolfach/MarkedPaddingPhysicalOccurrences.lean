module

public import Oberwolfach.MarkedPaddingDegrees
public import Oberwolfach.MarkedPaddingPacking
public import Oberwolfach.MarkedInitialDiagramIdentity

@[expose] public section

/-! Exact physical occurrence maps for a canonical padding wheel. Their
injectivity follows from the actual wheel packing, not from injectivity
of the map on old vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

def canonicalMarkedRimImage (π:Equiv.Perm V) (C:Fin (m+1)→V) (i:Fin (m+1)):Finset V:=
  if i=Fin.last m then {C i,π (C (finRotate (m+1) i))} else {C i,C (finRotate (m+1) i)}

theorem canonicalMarkedRimImage_eq (C:MarkedCycleTuple tail head ktail khead m π b) (i:Fin (m+1)):
    canonicalMarkedRimImage π C.val i=
      markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C i):=by
  refine Fin.lastCases ?_ (fun k=>?_) i
  · simp only [canonicalMarkedRimImage,ite_true,finRotate_last,markedCycleTypedEdge,Fin.snoc_last,
      markedPhysicalEdge,Sum.elim_inr]
    have he:=Classical.choose_spec C.property.2.2
    rw [he.1,he.2]
  · simp only [canonicalMarkedRimImage,Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ,
      markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,Sum.elim_inl]
    have he:=Classical.choose_spec (C.property.2.1 k)
    rw [he.1,he.2]

theorem canonicalMarkedRimImage_mem
    (C:MarkedWheel tail head ktail khead m π b H₀ HK) (k:Fin (m+1)):
    Sum.inl (canonicalMarkedRimImage π C.1.val k)∈markedWheelPhysicalResources C:=by
  apply (markedWheelPhysicalResources_rim C _).mpr
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,(canonicalMarkedRimImage_eq C.1 k).symm⟩

theorem marked_wheel_family_rim_injective
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    Function.Injective (fun z:I×Fin (m+1)=>canonicalMarkedRimImage π (C z.1).1.val z.2):=by
  rintro ⟨i,k⟩ ⟨j,k'⟩ he
  change canonicalMarkedRimImage π (C i).1.val k=canonicalMarkedRimImage π (C j).1.val k' at he
  have hij:i=j:=by
    by_contra hn
    exact Finset.disjoint_left.mp (hpack i j hn) (canonicalMarkedRimImage_mem (C i) k)
      (he.symm ▸ canonicalMarkedRimImage_mem (C j) k')
  subst j
  have hk:k=k':=markedCycle_distinct_physical_edges tail head ktail khead m π b hp (C i).1
    (by simpa only [canonicalMarkedRimImage_eq,Function.comp_apply] using he)
  exact Prod.ext rfl hk

theorem marked_wheel_family_spoke_injective
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    Function.Injective (fun z:I×Fin (m+1)=>((C z.1).1.val z.2,(C z.1).2.val)):=by
  rintro ⟨i,k⟩ ⟨j,k'⟩ he
  change ((C i).1.val k,(C i).2.val)=((C j).1.val k',(C j).2.val) at he
  have mem (i:I) (k:Fin (m+1)):
      Sum.inr ((C i).1.val k,(C i).2.val)∈markedWheelPhysicalResources (C i):=
    (markedWheelPhysicalResources_spoke (C i) _ _).mpr ⟨rfl,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩
  have hij:i=j:=by
    by_contra hn
    exact Finset.disjoint_left.mp (hpack i j hn) (mem i k) (he.symm ▸ mem j k')
  subst j
  have hk:k=k':=permutationSeparated_injective π b (C i).1.val (C i).1.property.1 (congrArg Prod.fst he)
  exact Prod.ext rfl hk

theorem marked_wheel_family_root_resources
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK):
    markedRootGraphResources π (fun z:I×Fin (m+1)=>(C z.1).1.val z.2)
      (fun z:I×Fin (m+1)=>(C z.1).1.val (finRotate (m+1) z.2))
      (fun z:I×Fin (m+1)=>(C z.1).1.val z.2)
      (fun z:I×Fin (m+1)=>decide (z.2=Fin.last m)) (fun z:I×Fin (m+1)=>(C z.1).2.val)=
      Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i)):=by
  ext e
  cases e with
  | inl e=>
    simp only [markedRootGraphResources,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
      Sum.inl.injEq,Sum.inr_ne_inl,exists_false,or_false,Finset.mem_biUnion,markedWheelPhysicalResources_rim]
    constructor
    · rintro ⟨⟨i,k⟩,he⟩
      refine ⟨i,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,?_⟩⟩
      simpa only [Function.comp_apply,←canonicalMarkedRimImage_eq,canonicalMarkedRimImage,decide_eq_true_eq] using he
    · rintro ⟨i,he⟩
      obtain ⟨k,_,hk⟩:=Finset.mem_image.mp he
      refine ⟨(i,k),?_⟩
      simpa only [Function.comp_apply,←canonicalMarkedRimImage_eq,canonicalMarkedRimImage,decide_eq_true_eq] using hk
  | inr vu=>
    rcases vu with ⟨v,u⟩
    simp only [markedRootGraphResources,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
      Sum.inl_ne_inr,exists_false,false_or,Sum.inr.injEq,Prod.mk.injEq,Finset.mem_biUnion,markedWheelPhysicalResources_spoke]
    constructor
    · rintro ⟨⟨i,k⟩,hk,hu⟩;exact ⟨i,hu,k,hk⟩
    · rintro ⟨i,hu,k,hk⟩;exact ⟨(i,k),hk,hu⟩

end Oberwolfach
