module

public import Oberwolfach.MarkedPaddingPhysicalOccurrences
public import Oberwolfach.ResourceFamilyIndicators

@[expose] public section

/-! The augmented graph is an actual disjoint union of old occurrences and
padding-wheel occurrences. Its physical edge maps are proved injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S I:Type} [Fintype A] [Fintype S] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

def actualPaddingSpokeHub (u:S→U) (h:I→U):S⊕(I×Fin (m+1))→U:=
  Sum.elim u (fun z=>h z.1)

theorem padded_rim_physical_map (src dst:A→V) (jr:A→Bool)
    (C:I→Fin (m+1)→V):
    (fun e=>if paddingRimType jr m e then
      ({paddingRimTail src C e,π (paddingRimHead dst C e)}:Finset V) else
      {paddingRimTail src C e,paddingRimHead dst C e})=
    Sum.elim (fun e=>if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e})
      (fun z:I×Fin (m+1)=>canonicalMarkedRimImage π (C z.1) z.2):=by
  funext e;cases e <;>
    simp only [paddingRimType,paddingRimTail,paddingRimHead,Sum.elim_inl,Sum.elim_inr,
      canonicalMarkedRimImage,decide_eq_true_eq]

theorem padded_graph_resources (src dst:A→V) (row:S→V) (jr:A→Bool) (u:S→U)
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK):
    markedRootGraphResources π (paddingRimTail src (fun i=>(C i).1.val))
      (paddingRimHead dst (fun i=>(C i).1.val)) (paddingSpokeRow row (fun i=>(C i).1.val))
      (paddingRimType jr m) (actualPaddingSpokeHub u (fun i=>(C i).2.val))=
    markedRootGraphResources π src dst row jr u∪Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i)):=by
  rw [←marked_wheel_family_root_resources C]
  ext e
  simp only [markedRootGraphResources,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,
    Sum.exists,paddingRimType,paddingRimTail,paddingRimHead,paddingSpokeRow,actualPaddingSpokeHub,
    Sum.elim_inl,Sum.elim_inr]
  tauto

theorem padded_graph_occurrences_injective (src dst:A→V) (row:S→V) (jr:A→Bool) (u:S→U)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))
    (hav:∀ i,Disjoint (markedWheelPhysicalResources (C i)) (markedRootGraphResources π src dst row jr u))
    (hr:Function.Injective (fun e=>if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e}))
    (hs:Function.Injective (fun s=>(row s,u s))):
    Function.Injective (fun e=>if paddingRimType jr m e then
      ({paddingRimTail src (fun i=>(C i).1.val) e,π (paddingRimHead dst (fun i=>(C i).1.val) e)}:Finset V) else
      {paddingRimTail src (fun i=>(C i).1.val) e,paddingRimHead dst (fun i=>(C i).1.val) e})∧
    Function.Injective (fun s=>(paddingSpokeRow row (fun i=>(C i).1.val) s,
      actualPaddingSpokeHub u (fun i=>(C i).2.val) s)):=by
  constructor
  · rw [padded_rim_physical_map]
    apply hr.sumElim (marked_wheel_family_rim_injective hp C hpack)
    intro a z he
    have ha:(Sum.inl (if jr a then ({src a,π (dst a)}:Finset V) else {src a,dst a}):Finset V⊕(V×U))∈
        markedRootGraphResources π src dst row jr u:=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    exact Finset.disjoint_left.mp (hav z.1) (canonicalMarkedRimImage_mem (C z.1) z.2) (he ▸ ha)
  · have heq:(fun s=>(paddingSpokeRow row (fun i=>(C i).1.val) s,actualPaddingSpokeHub u (fun i=>(C i).2.val) s))=
        Sum.elim (fun s=>(row s,u s)) (fun z:I×Fin (m+1)=>((C z.1).1.val z.2,(C z.1).2.val)):=by
      funext s;cases s <;> rfl
    rw [heq]
    apply hs.sumElim (marked_wheel_family_spoke_injective C hpack)
    intro a z he
    have ha:(Sum.inr (row a,u a):Finset V⊕(V×U))∈markedRootGraphResources π src dst row jr u:=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    have hz:(Sum.inr ((C z.1).1.val z.2,(C z.1).2.val):Finset V⊕(V×U))∈markedWheelPhysicalResources (C z.1):=
      (markedWheelPhysicalResources_spoke (C z.1) _ _).mpr ⟨rfl,Finset.mem_image.mpr ⟨z.2,Finset.mem_univ _,rfl⟩⟩
    exact Finset.disjoint_left.mp (hav z.1) hz (he ▸ ha)

end Oberwolfach
