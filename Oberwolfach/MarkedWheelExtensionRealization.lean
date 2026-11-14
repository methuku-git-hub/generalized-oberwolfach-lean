module

public import Oberwolfach.IndexedMarkedRealizationResources
public import Oberwolfach.IndexedMarkedWheelExtension
public import Oberwolfach.MarkedPaddedGraphOccurrences
public import Oberwolfach.MarkedPaddedArcSeparation

@[expose] public section

/-! The actual union of a realised old graph with a physical wheel packing,
retaining both the indexed graph and its exact resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S I:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S] [Fintype I]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

theorem indexedMarkedWheelExtension_actual_map (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V) (g:U₀→U) (C:I→MarkedWheel tail head ktail khead m π b H₀ HK):
    (indexedMarkedWheelExtension (I:=I) G m).map (Sum.elim f (fun z=>(C z.1).1.val z.2))
      (Sum.elim g (fun i=>(C i).2.val))=
    {src:=paddingRimTail (f∘G.src) (fun i=>(C i).1.val),
     dst:=paddingRimHead (f∘G.dst) (fun i=>(C i).1.val),
     row:=paddingSpokeRow (f∘G.row) (fun i=>(C i).1.val),
     hub:=actualPaddingSpokeHub (g∘G.hub) (fun i=>(C i).2.val),
     jr:=paddingRimType G.jr m,js:=paddingSpokeType G.js m}:=by
  apply indexedMarkedGraph_ext <;> funext a <;> cases a <;> rfl

def indexedMarkedWheelExtensionRealization (G:IndexedMarkedGraph V₀ U₀ A S)
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))
    (hav:∀ i,Disjoint (markedWheelPhysicalResources (C i)) R.resources):
    IndexedMarkedHostRealization (indexedMarkedWheelExtension (I:=I) G m) tail head ktail khead H₀ HK π b:=by
  have hpres:=padded_typed_presence (R.rows∘G.src) (R.rows∘G.dst) (R.rows∘G.row) G.jr G.js
    (R.hubs∘G.hub) C R.rimPresent R.spokePresent
  have hinj:=padded_graph_occurrences_injective (R.rows∘G.src) (R.rows∘G.dst) (R.rows∘G.row) G.jr
    (R.hubs∘G.hub) hp C hpack hav R.rimInjective R.spokeInjective
  let P:IndexedMarkedGraph V U (A⊕(I×Fin (m+1))) (S⊕(I×Fin (m+1))):=
    ⟨paddingRimTail (R.rows∘G.src) (fun i=>(C i).1.val),
     paddingRimHead (R.rows∘G.dst) (fun i=>(C i).1.val),
     paddingSpokeRow (R.rows∘G.row) (fun i=>(C i).1.val),
     actualPaddingSpokeHub (R.hubs∘G.hub) (fun i=>(C i).2.val),
     paddingRimType G.jr m,paddingSpokeType G.js m⟩
  let T:IndexedMarkedHostRealization P tail head ktail khead H₀ HK π b:=
    ⟨id,id,hpres.1,hpres.2,
      padded_arcs_separated (R.rows∘G.src) (R.rows∘G.dst) hm (fun i=>(C i).1) R.arcSeparated,hinj.1,hinj.2⟩
  exact IndexedMarkedHostRealization.ofMapEq _ T
    (Sum.elim R.rows (fun z=>(C z.1).1.val z.2)) (Sum.elim R.hubs (fun i=>(C i).2.val))
    (indexedMarkedWheelExtension_actual_map G R.rows R.hubs C)

theorem indexedMarkedWheelExtensionRealization_resources (G:IndexedMarkedGraph V₀ U₀ A S)
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))
    (hav:∀ i,Disjoint (markedWheelPhysicalResources (C i)) R.resources):
    (indexedMarkedWheelExtensionRealization G R hm hp C hpack hav).resources=
      R.resources∪Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i)):=by
  unfold indexedMarkedWheelExtensionRealization
  rw [IndexedMarkedHostRealization.resources_ofMapEq]
  exact padded_graph_resources (R.rows∘G.src) (R.rows∘G.dst) (R.rows∘G.row) G.jr (R.hubs∘G.hub) C

end Oberwolfach
