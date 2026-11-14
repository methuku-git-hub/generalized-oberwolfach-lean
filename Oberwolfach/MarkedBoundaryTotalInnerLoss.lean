module

public import Oberwolfach.MarkedSelectedBoundaryAfterPackings

@[expose] public section

/-! The approximate packing contributes no loss inside the next pair.
The later covering is charged at its actual physical degree. Column losses
are counted only on the inner row set, not on all ambient vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b m:ℕ}

theorem marked_packing_avoids_inner_pair
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (X:Finset V) (Z:Finset U)
    (hM:∀ e∈M.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e):
    (∀ x∈X,∀ y∈X,¬(markedPackingRimGraph M).Adj x y)∧
    (∀ x∈X,∀ u∈Z,¬markedPackingSpokes M x u):=by
  constructor
  · intro x hx y hy hxy
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp hxy.2
    apply hM (Sum.inl {x,y}) (Finset.mem_biUnion.mpr ⟨W,hW,(markedWheelPhysicalResources_rim W _).mpr he⟩)
    change ({x,y}:Finset V)⊆X
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy
  · intro x hx u hu hxu
    obtain ⟨W,hW,hh,hxW⟩:=hxu
    exact hM (Sum.inr (x,u)) (Finset.mem_biUnion.mpr ⟨W,hW,
      (markedWheelPhysicalResources_spoke W x u).mpr ⟨hh,hxW⟩⟩) ⟨hx,hu⟩

theorem marked_boundary_total_inner_loss
    (M₀ M₁ N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (X:Finset V) (Z:Finset U)
    (hM₀:∀ e∈M₀.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e)
    (δ₀ δr δs δu:ℝ)
    (hM₁:∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree z:ℝ)≤δ₀)
    (hr:∀ x,((spanningRestriction (markedPackingRimGraph N) X).degree x:ℝ)≤δr)
    (hs:∀ x∈X,((Z.filter (markedPackingSpokes N x)).card:ℝ)≤δs)
    (hu:∀ u∈Z,((Finset.univ.filter (fun x=>markedPackingSpokes N x u)).card:ℝ)≤δu):
    let M:=M₀∪M₁∪N
    (∀ x,((spanningRestriction (markedPackingRimGraph M) X).degree x:ℝ)≤δ₀+δr)∧
    (∀ x∈X,((Z.filter (markedPackingSpokes M x)).card:ℝ)≤δ₀+δs)∧
    (∀ u∈Z,((X.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤δ₀+δu):=by
  let D:=ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)
  have hzero:=marked_packing_avoids_inner_pair M₀ X Z hM₀
  have hR:∀ x,((markedPackingRimGraph M₁).degree x:ℝ)≤δ₀:=by
    intro x
    have hg:((D.comap (Sum.inl:V→V⊕U)).degree x:ℝ)≤D.degree (Sum.inl x):=by
      exact_mod_cast graph_comap_degree_le D ⟨Sum.inl,Sum.inl_injective⟩ x
    have he:D.comap (Sum.inl:V→V⊕U)=markedPackingRimGraph M₁:=by ext x y;rfl
    simp only [←SimpleGraph.ncard_neighborSet] at hg ⊢
    rw [he] at hg
    exact hg.trans (by simpa only [←SimpleGraph.ncard_neighborSet] using hM₁ (Sum.inl x))
  have hS (x:V):((Finset.univ.filter (markedPackingSpokes M₁ x)).card:ℝ)≤δ₀:=by
    have hh:=physical_spoke_deleted_row D x
    exact (Nat.cast_le.mpr hh).trans (hM₁ _)
  have hU (u:U):((Finset.univ.filter (fun x=>markedPackingSpokes M₁ x u)).card:ℝ)≤δ₀:=by
    have hh:=physical_spoke_deleted_col D u
    exact (Nat.cast_le.mpr hh).trans (hM₁ _)
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro x
    have hle:spanningRestriction (markedPackingRimGraph (M₀∪M₁∪N)) X≤
        markedPackingRimGraph M₁⊔spanningRestriction (markedPackingRimGraph N) X:=by
      intro v w hvw
      obtain ⟨he,hv,hw⟩:=(spanningRestriction_adj _ _ _ _).mp hvw
      rw [markedPackingRimGraph_union,markedPackingRimGraph_union] at he
      rcases he with (h0|h1)|hn
      · exact (hzero.1 v hv w hw h0).elim
      · exact Or.inl h1
      · exact Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨hn,hv,hw⟩)
    have hd:=((SimpleGraph.degree_le_of_le hle).trans
      (graph_degree_sup_le (markedPackingRimGraph M₁) (spanningRestriction (markedPackingRimGraph N) X) x))
    have hh:((spanningRestriction (markedPackingRimGraph (M₀∪M₁∪N)) X).degree x:ℝ)≤
        (markedPackingRimGraph M₁).degree x+(spanningRestriction (markedPackingRimGraph N) X).degree x:=by exact_mod_cast hd
    exact hh.trans (add_le_add (hR x) (hr x))
  · intro x hx
    have hsub:Z.filter (markedPackingSpokes (M₀∪M₁∪N) x)⊆
        Finset.univ.filter (markedPackingSpokes M₁ x)∪Z.filter (markedPackingSpokes N x):=by
      intro u hmem
      obtain ⟨hu,hm⟩:=Finset.mem_filter.mp hmem
      rw [markedPackingSpokes_union,markedPackingSpokes_union] at hm
      rcases hm with (h0|h1)|hn
      · exact (hzero.2 x hx u hu h0).elim
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,hn⟩)
    have hd:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh:((Z.filter (markedPackingSpokes (M₀∪M₁∪N) x)).card:ℝ)≤
        (Finset.univ.filter (markedPackingSpokes M₁ x)).card+(Z.filter (markedPackingSpokes N x)).card:=by exact_mod_cast hd
    exact hh.trans (add_le_add (hS x) (hs x hx))
  · intro u hz
    have hsub:X.filter (fun x=>markedPackingSpokes (M₀∪M₁∪N) x u)⊆
        Finset.univ.filter (fun x=>markedPackingSpokes M₁ x u)∪Finset.univ.filter (fun x=>markedPackingSpokes N x u):=by
      intro x hmem
      obtain ⟨hx,hm⟩:=Finset.mem_filter.mp hmem
      rw [markedPackingSpokes_union,markedPackingSpokes_union] at hm
      rcases hm with (h0|h1)|hn
      · exact (hzero.2 x hx u hz h0).elim
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    have hd:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh:((X.filter (fun x=>markedPackingSpokes (M₀∪M₁∪N) x u)).card:ℝ)≤
        (Finset.univ.filter (fun x=>markedPackingSpokes M₁ x u)).card+
        (Finset.univ.filter (fun x=>markedPackingSpokes N x u)).card:=by exact_mod_cast hd
    exact hh.trans (add_le_add (hU u) (hu u hz))

end Oberwolfach
