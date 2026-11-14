module

public import Oberwolfach.MarkedReservedRimPairCount
public import Oberwolfach.MarkedFiniteDeletionGraphBounds
public import Oberwolfach.MarkedApproximatePackingExclusions

@[expose] public section
/-! The reserved physical resources determine rim and spoke graphs. Their
degrees are at most the total number of reserved resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def markedReservedSpokePairs (C:Finset (Finset V⊕(V×U))):Finset (V×U):=
  Finset.univ.filter (fun z=>Sum.inr z∈C)

theorem marked_reserved_spoke_pairs_card (C:Finset (Finset V⊕(V×U))):
    (markedReservedSpokePairs C).card≤C.card :=by
  apply Finset.card_le_card_of_injOn Sum.inr
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro a _ b _ h
    exact Sum.inr.inj h

theorem marked_reserved_resource_graphs (C:Finset (Finset V⊕(V×U))):
    let R:=physicalEdgeGraph (markedReservedRimPairs C)
    let S:=markedFiniteSpokeGraph (markedReservedSpokePairs C);
    (∀ x y,R.Adj x y ↔ x≠y∧Sum.inl ({x,y}:Finset V)∈C)∧
    (∀ v u,S.Adj (Sum.inl v) (Sum.inr u) ↔ Sum.inr (v,u)∈C)∧
    (∀ x,R.degree x≤C.card)∧(∀ z,S.degree z≤C.card):=by
  intro R S
  refine ⟨?_,?_,?_,?_⟩
  · intro x y
    change x≠y∧({x,y}:Finset V)∈markedReservedRimPairs C ↔ _
    rw [marked_reserved_rim_pairs_membership]
  · intro v u
    rw [markedFiniteSpokeGraph_adj]
    simp [markedReservedSpokePairs]
  · intro x
    exact (physicalEdgeGraph_degree_le_incident _ x).trans
      ((Finset.card_filter_le _ _).trans (marked_reserved_rim_pairs_card C))
  · intro z
    obtain ⟨hrow,hcol⟩:=finite_spoke_graph_degree_counts (markedReservedSpokePairs C)
    cases z with
    | inl x=>exact (hrow x).trans ((Finset.card_filter_le _ _).trans (marked_reserved_spoke_pairs_card C))
    | inr u=>exact (hcol u).trans ((Finset.card_filter_le _ _).trans (marked_reserved_spoke_pairs_card C))

/-- Resources internal to a protected pair avoid the reserved-resource graphs
when the reserved set itself avoids that pair. -/
theorem marked_reserved_graphs_avoid_internal_resources
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hC:∀ e∈C,¬markedInnerResource I J e):
    let R:=physicalEdgeGraph (markedReservedRimPairs C)
    let S:=markedFiniteSpokeGraph (markedReservedSpokePairs C);
    (∀ x∈I,∀ y∈I,¬R.Adj x y) ∧
    (∀ v∈I,∀ u∈J,¬S.Adj (Sum.inl v) (Sum.inr u)):=by
  intro R S
  have hg:=marked_reserved_resource_graphs C
  constructor
  · intro x hx y hy hxy
    have he:Sum.inl ({x,y}:Finset V)∈C:=(hg.1 x y).mp hxy |>.2
    apply hC _ he
    change ({x,y}:Finset V)⊆I
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy
  · intro v hv u hu huv
    have he:Sum.inr (v,u)∈C:=(hg.2.1 v u).mp huv
    exact hC _ he ⟨hv,hu⟩

/-- In particular, prescribed typed arcs and spokes inside the pair remain
available after the reserved-resource graphs are removed. -/
theorem marked_reserved_graphs_preserve_prescribed_resources
    {E K:Type} (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let R:=physicalEdgeGraph (markedReservedRimPairs C)
    let S:=markedFiniteSpokeGraph (markedReservedSpokePairs C);
    (∀ a:E⊕K,Sum.elim tail ktail a∈I→Sum.elim head khead a∈I→
      Sum.elim (fun e=>s(tail e,head e)) (fun e=>s(ktail e,π (khead e))) a∉R.edgeFinset)∧
    (∀ v∈I,∀ u∈J,¬S.Adj (Sum.inl v) (Sum.inr u)):=by
  intro R S
  obtain ⟨hR,hS⟩:=marked_reserved_graphs_avoid_internal_resources C I J hC
  refine ⟨?_,hS⟩
  intro a ha hb
  cases a with
  | inl e=>
    simpa only [Sum.elim_inl,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hR (tail e) ha (head e) hb
  | inr e=>
    simpa only [Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hR (ktail e) ha (π (khead e)) ((hI _).mpr hb)

/-- A packing avoiding the two reserved graphs avoids every reserved physical
resource, including its marked rim and spoke types. -/
theorem marked_packing_avoiding_reserved_graphs
    {E K:Type} {tail head:E→V} {ktail khead:K→V} {m b:ℕ}
    {π:Equiv.Perm V} {H₀ HK:V→U→Prop} (hm:1≤m) (hb:1≤b)
    (C:Finset (Finset V⊕(V×U)))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hR:Disjoint (markedPackingRimGraph M) (physicalEdgeGraph (markedReservedRimPairs C)))
    (hS:∀ x u,markedPackingSpokes M x u→¬(markedFiniteSpokeGraph (markedReservedSpokePairs C)).Adj (Sum.inl x) (Sum.inr u)):
    Disjoint C (M.biUnion markedWheelPhysicalResources):=by
  apply Finset.disjoint_left.mpr
  intro e hC hM
  cases e with
  | inr z=>
    have hh:=(marked_reserved_resource_graphs C).2.1 z.1 z.2
    exact hS z.1 z.2 ((markedPackingResources_spoke M z.1 z.2).mp hM) (hh.mpr hC)
  | inl e=>
    have he:=(markedPackingResources_rim M e).mp hM
    obtain ⟨W,hW,hWe⟩:=Finset.mem_biUnion.mp he
    have hcard:e.card=2:=by
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hWe
      rw [←hi]
      exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb W.1 i
    obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp hcard
    have hMR:(markedPackingRimGraph M).Adj x y:=⟨hxy,Finset.mem_biUnion.mpr ⟨W,hW,hWe⟩⟩
    have hCR:(physicalEdgeGraph (markedReservedRimPairs C)).Adj x y:=
      ((marked_reserved_resource_graphs C).1 x y).mpr ⟨hxy,hC⟩
    exact disjoint_graphs_no_common_edge _ _ hR x y hMR hCR
end Oberwolfach
