module

public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Avoiding the actual rim and spoke graphs of an earlier packing proves
physical resource disjointness, even for different typed host descriptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V} {ktail' khead':K'→V}
  {m b m' b':ℕ} {π π':Equiv.Perm V} {H₀ HK H₀' HK':V→U→Prop}

theorem marked_packing_disjoint_from_deletion (hm:1≤m) (hb:1≤b)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hMR:markedPackingRimGraph M≤DR)
    (hMS:∀ x u,markedPackingSpokes M x u→DS.Adj (Sum.inl x) (Sum.inr u))
    (hNR:Disjoint (markedPackingRimGraph N) DR)
    (hNS:∀ x u,markedPackingSpokes N x u→¬DS.Adj (Sum.inl x) (Sum.inr u)):
    Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inr z=>
    exact hNS z.1 z.2 ((markedPackingResources_spoke N _ _).mp hf)
      (hMS z.1 z.2 ((markedPackingResources_spoke M _ _).mp he))
  | inl e=>
    have hem:=(markedPackingResources_rim M e).mp he
    have hen:=(markedPackingResources_rim N e).mp hf
    obtain ⟨C,hC,heC⟩:=Finset.mem_biUnion.mp hem
    have hcard:e.card=2:=by
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp heC
      rw [←hi]
      exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb C.1 i
    obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp hcard
    exact disjoint_graphs_no_common_edge _ _ hNR x y ⟨hxy,hen⟩
      (hMR ⟨hxy,Finset.mem_biUnion.mpr ⟨C,hC,heC⟩⟩)

end Oberwolfach
