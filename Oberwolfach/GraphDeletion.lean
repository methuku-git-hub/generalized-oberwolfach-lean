module

public import Oberwolfach.CycleCopies

@[expose] public section

/-! Exact degrees and edge counts under deletion of a contained graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_degree_sdiff {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : H ≤ G) (x : V) :
    (G \ H).degree x = G.degree x - H.degree x := by
  have heq : (G \ H).neighborFinset x = G.neighborFinset x \ H.neighborFinset x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff, SimpleGraph.sdiff_adj]
  have hs : H.neighborFinset x ⊆ G.neighborFinset x := by
    intro y hy
    simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact h hy
  rw [← SimpleGraph.card_neighborFinset_eq_degree, heq, Finset.card_sdiff_of_subset hs,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]

theorem graph_edge_count_sdiff {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : H ≤ G) :
    (G \ H).edgeFinset.card = G.edgeFinset.card - H.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_sdiff, Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono h)]

theorem mapped_regular_degree_or_zero {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) {d : ℕ}
    (hG : G.IsRegularOfDegree d) (f : V ↪ W) (x : W) :
    (G.map f).degree x = 0 ∨ (G.map f).degree x = d := by
  by_cases hx : x ∈ Set.range f
  · obtain ⟨v, rfl⟩ := hx
    right
    have hh := SimpleGraph.degree_map_apply G f v
    rw [hG v] at hh
    simpa only [← SimpleGraph.ncard_neighborSet] using hh
  · left
    have hiso : (G.map f).IsIsolated x := by
      intro y hxy
      rw [SimpleGraph.map_adj] at hxy
      obtain ⟨u, v, huv, hu, hv⟩ := hxy
      exact hx ⟨u, hu⟩
    exact hiso.degree_eq_zero

theorem graph_sdiff_even_degrees {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : H ≤ G)
    (hG : ∀ x, Even (G.degree x)) (hH : ∀ x, Even (H.degree x)) :
    ∀ x, Even ((G \ H).degree x) := by
  intro x
  rw [graph_degree_sdiff G H h x]
  exact (hG x).tsub (hH x)

theorem graph_filtered_edges_sdiff {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (P : Sym2 V → Prop) [DecidablePred P]
    (hP : ∀ e ∈ G.edgeFinset, P e → e ∉ H.edgeFinset) :
    (G \ H).edgeFinset.filter P = G.edgeFinset.filter P := by
  rw [SimpleGraph.edgeFinset_sdiff]
  ext e
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hP e h.1 h.2⟩, h.2⟩⟩

end Oberwolfach
