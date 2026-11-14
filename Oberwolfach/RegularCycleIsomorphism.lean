module

public import Oberwolfach.TwoRegularComponents
public import Oberwolfach.CycleCopies

@[expose] public section

/-! Actual cycle-graph isomorphisms for every component of a finite 2-factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_subgraph_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {d : ℕ}
    (hsub : H ≤ G) (hG : G.IsRegularOfDegree d) (hH : H.IsRegularOfDegree d) : H = G := by
  ext x y
  have hs : H.neighborFinset x ⊆ G.neighborFinset x := by
    intro z hz
    have hz' : H.Adj x z := by simpa only [SimpleGraph.mem_neighborFinset] using hz
    simpa only [SimpleGraph.mem_neighborFinset] using hsub hz'
  have hc : (G.neighborFinset x).card ≤ (H.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree,
      hG x, hH x]
  have heq := Finset.eq_of_subset_of_card_le hs hc
  simpa only [SimpleGraph.mem_neighborFinset] using
    (show y ∈ H.neighborFinset x ↔ y ∈ G.neighborFinset x by rw [heq])

theorem regular_copy_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
    (f : SimpleGraph.Copy H G) (hf : Function.Surjective f)
    (hG : G.IsRegularOfDegree d) (hH : H.IsRegularOfDegree d) :
    Nonempty (H ≃g G) := by
  let e : W ≃ V := Equiv.ofBijective f ⟨f.injective, hf⟩
  have hmap : (H.map e.toEmbedding).IsRegularOfDegree d := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    have hh := SimpleGraph.degree_map_apply H e.toEmbedding y
    rw [hH y] at hh
    simpa only [Equiv.toEmbedding_apply, ← SimpleGraph.ncard_neighborSet] using hh
  have hle : H.map e.toEmbedding ≤ G := by
    apply SimpleGraph.map_le_iff_le_comap.mpr
    intro u v huv
    exact f.toHom.map_adj huv
  have heq := regular_subgraph_eq hle hG (by
    intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using hmap v)
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro u v
  rw [← heq]
  exact SimpleGraph.map_adj_apply

theorem connected_regular_two_cycle_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsRegularOfDegree 2) (hconn : G.Connected) :
    3 ≤ Fintype.card V ∧ Nonempty (SimpleGraph.cycleGraph (Fintype.card V) ≃g G) := by
  let v : V := Classical.choice hconn.nonempty
  obtain ⟨p, hp, hs, hlen, _⟩ := regular_two_component_cycle G hG v
  have hlen' : p.length = Fintype.card V := by
    change p.length = ({x | G.Reachable v x} : Set V).ncard at hlen
    have heq : ({x | G.Reachable v x} : Set V) = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hconn.preconnected v x
    simpa only [heq, Set.ncard_univ, Nat.card_eq_fintype_card] using hlen
  have hthree : 3 ≤ Fintype.card V := by rw [← hlen']; exact hp.three_le_length
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < Fintype.card V)).mpr
    ⟨v, p, hp, hlen'⟩
  have hf : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp⟩).2
  exact ⟨hthree, regular_copy_iso f hf hG (by
    intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using cycleGraph_regular hthree v)⟩

theorem component_regular_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hG : G.IsRegularOfDegree d)
    (C : G.ConnectedComponent) [Fintype C] :
    C.toSimpleGraph.IsRegularOfDegree d := by
  intro v
  let e : C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val := {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, C.mem_supp_of_adj_mem_supp v.property w.property⟩, w.property⟩
    left_inv := by intro w; rfl
    right_inv := by intro w; rfl }
  have hc : (C.toSimpleGraph.neighborSet v).ncard = (G.neighborSet v.val).ncard :=
    Nat.card_congr e
  rw [← SimpleGraph.ncard_neighborSet, hc, SimpleGraph.ncard_neighborSet, hG v.val]

theorem component_regular_two_cycle_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsRegularOfDegree 2)
    (C : G.ConnectedComponent) [Fintype C] :
    3 ≤ Fintype.card C ∧ Nonempty (SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph) :=
  connected_regular_two_cycle_iso C.toSimpleGraph (component_regular_degree G hG C)
    C.connected_toSimpleGraph

end Oberwolfach
