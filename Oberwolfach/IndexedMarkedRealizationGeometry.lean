module

public import Oberwolfach.IndexedMarkedHostRealization

@[expose] public section

/-! Actual row and hub supports of a realised marked graph. Resource
disjointness uses the host's physical map, not the auxiliary endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V₁ U₁ V U E K A S A' S':Type}
    [Fintype V₀] [Fintype U₀] [Fintype A] [Fintype S]
    [Fintype V₁] [Fintype U₁] [Fintype A'] [Fintype S']
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

def IndexedMarkedHostRealization.rowSet {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):Finset V:=Finset.univ.image R.rows
def IndexedMarkedHostRealization.hubSet {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):Finset U:=Finset.univ.image R.hubs

theorem IndexedMarkedHostRealization.row_mem {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b) (v:V₀):R.rows v∈R.rowSet:=
  Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
theorem IndexedMarkedHostRealization.hub_mem {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b) (u:U₀):R.hubs u∈R.hubSet:=
  Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩

theorem IndexedMarkedHostRealization.rowSet_card {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):R.rowSet.card≤Fintype.card V₀:=
  Finset.card_image_le.trans (by simp)
theorem IndexedMarkedHostRealization.hubSet_card {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):R.hubSet.card≤Fintype.card U₀:=
  Finset.card_image_le.trans (by simp)

theorem IndexedMarkedHostRealization.resources_supported {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b):
    ∀ e∈R.resources,MarkedOldResource tail head ktail khead π R.rowSet R.hubSet e∧
      MarkedResourceSupported tail head ktail khead π R.rowSet e:=
  marked_root_graph_old_supported _ _ _ _ _ R.rowSet R.hubSet
    (fun a=>⟨R.row_mem _,R.row_mem _⟩) (fun s=>⟨R.row_mem _,R.hub_mem _⟩) R.rimPresent

theorem IndexedMarkedHostRealization.resources_disjoint
    {G:IndexedMarkedGraph V₀ U₀ A S} {G':IndexedMarkedGraph V₁ U₁ A' S'}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (T:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hrows:Disjoint R.rowSet T.rowSet):Disjoint R.resources T.resources:=by
  apply marked_resource_sets_disjoint hp R.rowSet T.rowSet hrows R.resources T.resources
  · exact fun e he=>(R.resources_supported e he).2
  · exact fun e he=>(T.resources_supported e he).2

end Oberwolfach
