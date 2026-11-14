module

public import Oberwolfach.MarkedRootPaddingConstruction

@[expose] public section

/-! Exact endpoint identities and removal of the constructed padding.
The physical edge representation and all old multiplicities are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}
    {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}

theorem MarkedRootPadding.source_resources (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    (P.pair hm hp).source=G.source∪pairedPaddingResources P.C false:=
  padded_graph_resources G.src G.dst G.row G.jr G.u (fun i=>P.C (false,i))

theorem MarkedRootPadding.image_resources (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    (P.pair hm hp).image=G.image∪pairedPaddingResources P.C true:=by
  have hmaps:=padded_maps_compatible G.src G.dst G.row G.u G.φ P.φ G.ψ P.ψ m
    (fun i=>(P.C (false,i)).1.val) (fun i=>(P.C (true,i)).1.val)
    (fun i=>(P.C (false,i)).2.val) (fun i=>(P.C (true,i)).2.val) (G.R∪G.R') G.B
    (fun a=>⟨Finset.mem_union_left _ (G.rimRoots a).1,Finset.mem_union_left _ (G.rimRoots a).2.1⟩)
    (fun s=>Finset.mem_union_left _ (G.spokeRoots s).1) (fun s=>(G.hubRoots s).1) P.oldRows P.oldHubs P.mapCycles
    (fun i=>by rw [(P.hubs (false,i)).1,(P.hubs (true,i)).1];exact P.mapHubs i)
  change markedRootGraphResources π
    (fun a=>P.φ (paddingRimTail G.src (fun i=>(P.C (false,i)).1.val) a))
    (fun a=>P.φ (paddingRimHead G.dst (fun i=>(P.C (false,i)).1.val) a))
    (fun s=>P.φ (paddingSpokeRow G.row (fun i=>(P.C (false,i)).1.val) s))
    (paddingRimType G.jr m) (actualPaddingSpokeHub G.u' (fun i=>(P.C (true,i)).2.val))=_
  simp only [hmaps.1,hmaps.2.1,hmaps.2.2.1]
  exact padded_graph_resources (fun a=>G.φ (G.src a)) (fun a=>G.φ (G.dst a)) (fun s=>G.φ (G.row s))
    G.jr G.u' (fun i=>P.C (true,i))

theorem MarkedRootPadding.remove (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (T:Finset (Finset V⊕(V×U)))
    (hT:IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) (P.pair hm hp).source (P.pair hm hp).image T):
    IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) G.source G.image
      (T∪pairedPaddingResources P.C false∪pairedPaddingResources P.C true):=by
  rw [P.source_resources hm hp,P.image_resources hm hp] at hT
  exact marked_transformer_unpad hm hp P.C (fun i=>if i.1 then G.φ i.2.val else i.2.val)
    P.p (G.R∪G.R') G.B P.coordinates (fun i k=>(P.avoid i k).2.1)
    (fun i=>by rw [(P.hubs i).1];exact (P.hubs i).2) P.packing G.source G.image T G.old_resources hT

theorem MarkedRootPadding.no_old_resource (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∀ j,∀ e∈pairedPaddingResources P.C j,¬MarkedOldResource tail head ktail khead π (G.R∪G.R') G.B e:=by
  intro j e he hold
  obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he
  have hd:=marked_padding_avoids_old_resources hm hp (P.C (j,i))
    (if j then G.φ i.val else i.val) (P.p (j,i)) (G.R∪G.R') G.B (P.coordinates (j,i))
    (fun k=>(P.avoid (j,i) k).2.1) (by rw [(P.hubs (j,i)).1];exact (P.hubs (j,i)).2)
    {e} (by intro e' he';have heq:=Finset.mem_singleton.mp he';subst e';cases e with
             | inl e=>exact hold
             | inr vu=>exact hold.2)
  exact Finset.disjoint_left.mp hd he (Finset.mem_singleton_self _)

theorem MarkedRootPadding.supported (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∀ j,∀ e∈pairedPaddingResources P.C j,
      MarkedResourceSupported tail head ktail khead π ((P.pair hm hp).R∪(P.pair hm hp).R') e:=by
  intro j e he
  obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he
  rw [markedWheelPhysicalResources_eq_atHub] at he
  apply marked_cycle_at_hub_supported (P.C (j,i)).1 (P.C (j,i)).2.val _ ?_ e he
  intro k
  have hh:=paired_padding_cycle_row_mem P.p Subtype.val (fun i:G.Exceptional=>G.φ i.val)
    G.R G.R' G.exceptional_roots j i k
  have he:(P.C (j,i)).1.val k=Fin.cons (α:=fun _=>V) (if j then G.φ i.val else i.val) (P.p (j,i)) k:=P.coordinates (j,i) k
  rw [←he] at hh
  cases j
  · exact Finset.mem_union_left _ hh
  · exact Finset.mem_union_right _ hh

theorem MarkedRootPadding.spoke_hubs (P:MarkedRootPadding G W):
    ∀ j v z,Sum.inr (v,z)∈pairedPaddingResources P.C j→z∈Finset.univ.image P.hub:=by
  intro j v z he
  obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he
  have hz:=((markedWheelPhysicalResources_spoke (P.C (j,i)) v z).mp he).1
  exact Finset.mem_image.mpr ⟨(j,i),Finset.mem_univ _,(P.hubs (j,i)).1.symm.trans hz⟩

end Oberwolfach
