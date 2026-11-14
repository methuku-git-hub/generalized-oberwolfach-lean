module

public import Oberwolfach.MarkedPackingEmbeddingDegrees

@[expose] public section

/-! Inner rim degrees and restricted spoke counts are preserved exactly
by an active-domain embedding. Vertices outside the image contribute no
rim or spoke incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem spanningRestriction_map_preimage {V W:Type} [DecidableEq V] [DecidableEq W]
    (G:SimpleGraph V) (f:V↪W) (X:Finset V) (I:Finset W)
    (hX:∀ v,f v∈I↔v∈X):
    spanningRestriction (G.map f) I=(spanningRestriction G X).map f:=by
  ext a b
  rw [spanningRestriction_adj,SimpleGraph.map_adj,SimpleGraph.map_adj]
  constructor
  · rintro ⟨⟨v,w,hvw,rfl,rfl⟩,hv,hw⟩
    exact ⟨v,w,(spanningRestriction_adj G X v w).mpr ⟨hvw,(hX v).mp hv,(hX w).mp hw⟩,rfl,rfl⟩
  · rintro ⟨v,w,hvw,rfl,rfl⟩
    obtain ⟨hvw,hv,hw⟩:=(spanningRestriction_adj G X v w).mp hvw
    exact ⟨⟨v,w,hvw,rfl,rfl⟩,(hX v).mpr hv,(hX w).mpr hw⟩

variable {V U V' U' E K E' K':Type}
  [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V'} {ktail' khead':K'→V'}
  {m b m' b':ℕ} {π:Equiv.Perm V} {π':Equiv.Perm V'}
  {H₀ HK:V→U→Prop} {H₀' HK':V'→U'→Prop}

theorem markedPackingResources_embedding_inner_degrees
    (f:V↪V') (g:U↪U')
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:N.biUnion markedWheelPhysicalResources=(M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f g))
    (X:Finset V) (Z:Finset U) (I:Finset V') (J:Finset U')
    (hX:∀ x,f x∈I↔x∈X) (hZ:∀ u,g u∈J↔u∈Z):
    (∀ v,(spanningRestriction (markedPackingRimGraph N) I).degree (f v)=
      (spanningRestriction (markedPackingRimGraph M) X).degree v)∧
    (∀ v,(J.filter (markedPackingSpokes N (f v))).card=(Z.filter (markedPackingSpokes M v)).card)∧
    (∀ u,(I.filter (fun x=>markedPackingSpokes N x (g u))).card=(X.filter (fun x=>markedPackingSpokes M x u)).card):=by
  obtain ⟨hr,hs⟩:=markedPackingResources_embedding_graphs f g M N he
  refine ⟨?_,?_,?_⟩
  · intro v
    simp only [←SimpleGraph.ncard_neighborSet]
    rw [hr,spanningRestriction_map_preimage _ f X I hX,SimpleGraph.neighborSet_map,
      Set.ncard_image_of_injective _ f.injective]
  · intro v
    have hh:J.filter (markedPackingSpokes N (f v))=(Z.filter (markedPackingSpokes M v)).image g:=by
      ext u
      simp only [Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨hu,hs'⟩
        obtain ⟨v',w,hv,hw,hm⟩:=(hs _ _).mp hs'
        have hv':v'=v:=f.injective hv
        subst v'
        exact ⟨w,⟨(hZ w).mp (hw.symm ▸ hu),hm⟩,hw⟩
      · rintro ⟨w,⟨hw,hm⟩,rfl⟩
        exact ⟨(hZ w).mpr hw,(hs _ _).mpr ⟨v,w,rfl,rfl,hm⟩⟩
    rw [hh,Finset.card_image_of_injective _ g.injective]
  · intro u
    have hh:I.filter (fun x=>markedPackingSpokes N x (g u))=(X.filter (fun x=>markedPackingSpokes M x u)).image f:=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨hv,hs'⟩
        obtain ⟨w,u',hw,hu,hm⟩:=(hs _ _).mp hs'
        have hu':u'=u:=g.injective hu
        subst u'
        exact ⟨w,⟨(hX w).mp (hw.symm ▸ hv),hm⟩,hw⟩
      · rintro ⟨w,⟨hw,hm⟩,rfl⟩
        exact ⟨(hX w).mpr hw,(hs _ _).mpr ⟨w,u,rfl,rfl,hm⟩⟩
    rw [hh,Finset.card_image_of_injective _ f.injective]

end Oberwolfach
