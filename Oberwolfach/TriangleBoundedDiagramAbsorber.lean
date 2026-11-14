module

public import Oberwolfach.TriangleActualDiagramAbsorber

@[expose] public section
/-! Derive the finite forbidden resource set and its bounds from the rows
and hubs of the actual diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_bounded_diagram_absorber (β:ℝ) (hβ:0<β):
  ∃ ε₀:ℝ,0<ε₀ ∧ ∀ M f:ℕ,∃ N₀ K₀:ℕ,
  ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
  ∀ (Q:SimpleGraph V) (H:V→U→Prop)
    (original:Finset (Sym2 V⊕(V×U))) (A W R₀:Finset V) (B₀ O:Finset U)
    (D:OrdinaryHostDiagram 3 M Q ⊥ H original A W R₀ B₀ O),
    W.card≤f→R₀.card≤f→B₀.card≤f→
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))→
  ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))→
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))→
  ∃ C:Finset (Sym2 V⊕(V×U)),
    IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) original C ∧
    C⊆ordinaryHostResources Q H ∧
    (ordinaryResourceRows C).card≤5*M+2*f+4*K₀ ∧
    (ordinaryResourceHubs C).card≤5*M+2*f+4*K₀ ∧
    Disjoint C (ordinaryRootResources (R₀∪W) B₀) :=by
  obtain ⟨ε₀,hε₀,hbase⟩:=triangle_actual_diagram_absorber β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro M f
  let q:=5*M+2*f
  obtain ⟨N₀,K₀,habs⟩:=hbase q
  refine ⟨N₀,K₀,?_⟩
  intro V U _ _ _ _ hn hU Q H original A W R₀ B₀ O D hW hR hB hdeg ε hε hεsmall hnearV hnearU
  let L:=Finset.univ.biUnion D.D∪ordinaryRootResources (R₀∪W) B₀
  have hr:ordinaryResourceRows L⊆D.rows∪(R₀∪W):=by
    dsimp [L]
    rw [ordinaryResourceRows_union,ordinaryResourceRows_biUnion]
    exact Finset.union_subset_union (Finset.biUnion_subset.mpr (fun i _=>D.Drows i))
      (ordinaryRootResources_rows _ _)
  have hu:ordinaryResourceHubs L⊆D.hubs∪B₀:=by
    dsimp [L]
    rw [ordinaryResourceHubs_union,ordinaryResourceHubs_biUnion]
    exact Finset.union_subset_union (Finset.biUnion_subset.mpr (fun i _=>D.Dhubs i))
      (ordinaryRootResources_hubs _ _)
  have hLr:(ordinaryResourceRows L).card≤q:=by
    have hcard:=Finset.card_le_card hr
    have hrow:=Finset.card_union_le D.rows (R₀∪W)
    have hRW:=Finset.card_union_le R₀ W
    have hm:=D.rows_card
    dsimp [q]
    omega
  have hLu:(ordinaryResourceHubs L).card≤q:=by
    have hcard:=Finset.card_le_card hu
    have hhub:=Finset.card_union_le D.hubs B₀
    have hm:=D.hubs_card
    dsimp [q]
    omega
  have hL:∀ i,D.D i⊆L:=fun i=>(Finset.subset_biUnion_of_mem D.D (Finset.mem_univ i)).trans Finset.subset_union_left
  have hroot:ordinaryRootResources (R₀∪W) B₀⊆L:=Finset.subset_union_right
  obtain ⟨T,_,_,habs,hhost,hrows,hhubs,havoid⟩:=habs V U hn hU Q H M original A W R₀ B₀ O D L
    (by dsimp [q];omega) hLr hLu hL hroot hdeg ε hε hεsmall hnearV hnearU
  refine ⟨ordinaryDiagramAbsorberEdges D T,habs,hhost,?_,?_,havoid⟩
  · simpa [q] using hrows
  · simpa [q] using hhubs
end Oberwolfach
