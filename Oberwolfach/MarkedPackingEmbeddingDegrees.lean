module

public import Oberwolfach.MarkedResourceEmbeddingGeometry
public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.PhysicalEdgeGraphEmbedding

@[expose] public section

/-! Exact rim graphs and spoke relations after embedding an active packing
back into the original vertex sets. Consequently no degree loss is introduced
by changing the vertex representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' E K E' K':Type}
  [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b m' b':ℕ} {π:Equiv.Perm V} {π':Equiv.Perm V'}
  {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem markedPackingResources_embedding_graphs
    (f:V↪V') (g:U↪U')
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:N.biUnion markedWheelPhysicalResources=(M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f g)):
    markedPackingRimGraph N=(markedPackingRimGraph M).map f∧
      (∀ x u,markedPackingSpokes N x u↔∃ v w,f v=x∧g w=u∧markedPackingSpokes M v w):=by
  have hr:markedPackingRims N=(markedPackingRims M).image (Finset.image f):=by
    ext e
    rw [←markedPackingResources_rim,he]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a,ha,he⟩
      cases a with
      | inl a=>exact ⟨a,(markedPackingResources_rim M a).mp ha,Sum.inl.inj he⟩
      | inr a=>exact (Sum.inr_ne_inl he).elim
    · rintro ⟨a,ha,he⟩
      exact ⟨Sum.inl a,(markedPackingResources_rim M a).mpr ha,congrArg Sum.inl he⟩
  constructor
  · unfold markedPackingRimGraph
    rw [hr,physicalEdgeGraph_image_map]
  · intro x u
    rw [←markedPackingResources_spoke,he]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a,ha,he⟩
      cases a with
      | inl a=>exact (Sum.inl_ne_inr he).elim
      | inr a=>
        have h: (f a.1,g a.2)=(x,u):=Sum.inr.inj he
        exact ⟨a.1,a.2,congrArg Prod.fst h,congrArg Prod.snd h,(markedPackingResources_spoke M _ _).mp ha⟩
    · rintro ⟨v,w,hv,hw,hM⟩
      exact ⟨Sum.inr (v,w),(markedPackingResources_spoke M v w).mpr hM,by
        change Sum.inr (f v,g w)=Sum.inr (x,u)
        rw [hv,hw]⟩

theorem markedPackingResources_embedding_rim_degree
    (f:V↪V') (g:U↪U')
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:N.biUnion markedWheelPhysicalResources=(M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f g))
    (v:V):
    (markedPackingRimGraph N).degree (f v)=(markedPackingRimGraph M).degree v:=by
  simp only [←SimpleGraph.ncard_neighborSet]
  rw [(markedPackingResources_embedding_graphs f g M N he).1,SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ f.injective]

end Oberwolfach
