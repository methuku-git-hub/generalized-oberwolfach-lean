module

public import Oberwolfach.MarkedWheelExtensionRealization
public import Oberwolfach.IndexedMarkedWheelUnion

@[expose] public section

/-! A disjoint family of actual marked wheels realises the finite abstract
wheel union, with equality of physical edge sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def emptyIndexedMarkedHostRealization:
    IndexedMarkedHostRealization emptyIndexedMarkedGraph tail head ktail khead H₀ HK π b:=
  ⟨Empty.elim,Empty.elim,(fun a=>a.elim),(fun s=>s.elim),(fun a=>a.elim),(fun a=>a.elim),(fun s=>s.elim)⟩

@[simp] theorem emptyIndexedMarkedHostRealization_resources:
    (emptyIndexedMarkedHostRealization (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (H₀:=H₀) (HK:=HK) (π:=π) (b:=b)).resources=∅:=by
  simp [IndexedMarkedHostRealization.resources,markedRootGraphResources]

def indexedMarkedWheelUnionRealization (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    IndexedMarkedHostRealization (indexedMarkedWheelUnion I m) tail head ktail khead H₀ HK π b:=by
  let T:=indexedMarkedWheelExtensionRealization emptyIndexedMarkedGraph emptyIndexedMarkedHostRealization hm hp C hpack (by simp)
  apply IndexedMarkedHostRealization.ofMapEq _ T (fun z=>(C z.1).1.val z.2) (fun i=>(C i).2.val)
  apply indexedMarkedGraph_ext <;> funext a <;> rcases a with a|⟨i,k⟩
  all_goals first | exact a.elim | rfl

theorem indexedMarkedWheelUnionRealization_resources (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    (indexedMarkedWheelUnionRealization hm hp C hpack).resources=
      Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i)):=by
  unfold indexedMarkedWheelUnionRealization
  rw [IndexedMarkedHostRealization.resources_ofMapEq,indexedMarkedWheelExtensionRealization_resources]
  simp only [emptyIndexedMarkedHostRealization_resources,Finset.empty_union]

end Oberwolfach
