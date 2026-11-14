module

public import Oberwolfach.MarkedPrescribedRimGeometry
public import Oberwolfach.MarkedPaddedArcSeparation

@[expose] public section

/-! Exact intersections with an inner pair of vertex sets. Invariance of
I under the physical successor permutation is needed when a marked head
is tested for membership in I. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def markedInnerResource (I:Finset V) (J:Finset U):Finset V⊕(V×U)→Prop:=
  Sum.elim (fun e=>e⊆I) (fun p=>p.1∈I∧p.2∈J)

theorem marked_cycle_edge_inside_iff (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (C:MarkedCycleTuple tail head ktail khead m π b) (a:Fin (m+1)):
    markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C a)⊆I↔
      C.val a∈I∧C.val (finRotate (m+1) a)∈I:=by
  rw [markedCycle_physical_pair]
  refine Fin.lastCases ?_ (fun a=>?_) a
  · simp only [twistedTupleHead,Fin.snoc_last,finRotate_last,Finset.insert_subset_iff,
      Finset.singleton_subset_iff,hI]
  · simp only [twistedTupleHead,Fin.snoc_castSucc,finRotate_castSucc_eq_succ,
      Finset.insert_subset_iff,Finset.singleton_subset_iff]

theorem marked_one_root_inner_resources (hm:0<m) (I:Finset V) (J:Finset U)
    (hI:∀ v,π v∈I↔v∈I) (C:MarkedWheel tail head ktail khead m π b H₀ HK)
    (x:V) (hx:x∈I) (hCx:x∈markedWheelRows C) (hCu:C.2.val∈J)
    (hrows:∀ a∈markedWheelRows C,a∈I→a=x):
    (markedWheelPhysicalResources C).filter (markedInnerResource I J)={Sum.inr (x,C.2.val)}:=by
  ext e
  cases e with
  | inl e=>
    simp only [Finset.mem_filter,markedInnerResource,Sum.elim_inl,Finset.mem_singleton,Sum.inl_ne_inr,iff_false]
    rintro ⟨he,hsub⟩
    rw [markedWheelPhysicalResources_rim] at he
    obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he
    have hinside:markedPhysicalEdge tail head ktail khead π
        (markedCycleTypedEdge tail head ktail khead m π b C.1 a)⊆I:=by rw [←ha] at hsub;exact hsub
    have hh:=(marked_cycle_edge_inside_iff I hI C.1 a).mp hinside
    have h1:=hrows (C.1.val a) (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) hh.1
    have h2:=hrows (C.1.val (finRotate (m+1) a))
      (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩) hh.2
    exact finRotate_ne_self_of_pos hm a (permutationSeparated_injective π b C.1.val C.1.property.1 (h1.trans h2.symm))
  | inr p=>
    rcases p with ⟨v,u⟩
    simp only [Finset.mem_filter,markedInnerResource,Sum.elim_inr,markedWheelPhysicalResources_spoke,
      Finset.mem_singleton,Sum.inr.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hu,hv⟩,hvI,huJ⟩
      exact ⟨hrows v hv hvI,hu.symm⟩
    · rintro ⟨rfl,rfl⟩;exact ⟨⟨rfl,hCx⟩,hx,hCu⟩

theorem marked_rim_root_inner_resources (I:Finset V) (J:Finset U)
    (hI:∀ v,π v∈I↔v∈I) (C:MarkedWheel tail head ktail khead m π b H₀ HK)
    (e₀:Finset V) (he₀:e₀⊆I) (hCe:Sum.inl e₀∈markedWheelPhysicalResources C) (hCu:C.2.val∉J)
    (hroot:∀ a,C.1.val a∈I→C.1.val (finRotate (m+1) a)∈I→
      markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C.1 a)=e₀):
    (markedWheelPhysicalResources C).filter (markedInnerResource I J)={Sum.inl e₀}:=by
  ext e
  cases e with
  | inl e=>
    simp only [Finset.mem_filter,markedInnerResource,Sum.elim_inl,Finset.mem_singleton,Sum.inl.injEq]
    constructor
    · rintro ⟨he,hsub⟩
      rw [markedWheelPhysicalResources_rim] at he
      obtain ⟨a,_,ha⟩:=Finset.mem_image.mp he
      have hinside:markedPhysicalEdge tail head ktail khead π
          (markedCycleTypedEdge tail head ktail khead m π b C.1 a)⊆I:=by rw [←ha] at hsub;exact hsub
      have hh:=(marked_cycle_edge_inside_iff I hI C.1 a).mp hinside
      exact ha.symm.trans (hroot a hh.1 hh.2)
    · rintro rfl;exact ⟨hCe,he₀⟩
  | inr p=>
    simp only [Finset.mem_filter,markedInnerResource,Sum.elim_inr,Finset.mem_singleton,Sum.inr_ne_inl,iff_false]
    rintro ⟨he,hv,hu⟩
    have hh:=(markedWheelPhysicalResources_spoke C p.1 p.2).mp he
    exact hCu (hh.1 ▸ hu)

end Oberwolfach
