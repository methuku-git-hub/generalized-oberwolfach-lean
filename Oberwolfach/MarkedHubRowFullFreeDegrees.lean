module

public import Oberwolfach.MarkedHubRowProtectedBounds
public import Oberwolfach.MarkedPhysicalRimDeletionDegrees

@[expose] public section

/-! Recover full physical degrees at free vertices from the induced-free
bound and the explicit root support. Edges joining a free vertex to an old
root are counted; they are not discarded by the restriction to F. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b n:ℕ} {H₀ HK:V→U→Prop}

theorem supported_graph_full_free_degree (G:SimpleGraph V) (F R:Finset V)
    (hs:GraphSupportedOn (F∪R) G) (x:V) (hx:x∈F):
    G.degree x≤(spanningRestriction G F).degree x+R.card:=by
  have hsub:G.neighborFinset x⊆(spanningRestriction G F).neighborFinset x∪R:=by
    intro y hy
    have hxy:=(G.mem_neighborFinset x y).mp hy
    rcases Finset.mem_union.mp (hs x y hxy).2 with hyF|hyR
    · exact Finset.mem_union_left _ ((spanningRestriction G F).mem_neighborFinset x y |>.mpr
        ((spanningRestriction_adj G F x y).mpr ⟨hxy,hx,hyF⟩))
    · exact Finset.mem_union_right _ hyR
  have hc:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hc

theorem marked_packing_supported_on_rows_and_images
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (F R:Finset V)
    (hF:∀ x,π x∈F↔x∈F) (hrows:∀ W∈M,markedWheelRows W⊆F∪R):
    GraphSupportedOn (F∪(R∪R.image π)) (markedPackingRimGraph M):=by
  intro x y hxy
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp hxy.2
  have hs:=markedWheelRimGraph_supported W x y ⟨hxy.1,he⟩
  have hsub:markedWheelRows W∪(markedWheelRows W).image π⊆F∪(R∪R.image π):=by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · rcases Finset.mem_union.mp (hrows W hW hz) with hz|hz
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hz)
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hz
      rcases Finset.mem_union.mp (hrows W hW ha) with ha|ha
      · exact Finset.mem_union_left _ ((hF a).mpr ha)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  exact ⟨hsub hs.1,hsub hs.2⟩

theorem marked_hub_row_full_free_rim_degree
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v:Fin n→V) (F:Finset V) (hF:∀ x,π x∈F↔x∈F)
    (hrows:∀ W∈M,markedWheelRows W⊆F∪Finset.univ.image v)
    (D:ℕ) (hdeg:∀ x,(spanningRestriction (markedPackingRimGraph M) F).degree x≤D):
    ∀ x∈F,(markedPackingRimGraph M).degree x≤D+2*n:=by
  let R:=Finset.univ.image v
  have hc:R.card≤n:=by exact (Finset.card_image_le).trans_eq (by simp)
  have hci:(R.image π).card≤n:=Finset.card_image_le.trans hc
  have htot:(R∪R.image π).card≤2*n:=by
    have hh:=(Finset.card_union_le R (R.image π)).trans (Nat.add_le_add hc hci)
    omega
  intro x hx
  have hh:=supported_graph_full_free_degree (markedPackingRimGraph M) F (R∪R.image π)
    (marked_packing_supported_on_rows_and_images M F R hF hrows) x hx
  exact hh.trans (Nat.add_le_add (hdeg x) htot)

end Oberwolfach
