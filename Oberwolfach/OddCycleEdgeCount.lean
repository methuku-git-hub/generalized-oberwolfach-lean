module

public import Oberwolfach.DecompositionCounts

@[expose] public section

/-! An odd-cycle decomposition consumes an edge of every two-colour obstruction
in each of its cycles. The count is on the physical edges, with no multiplicity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem IsCycleCopy.meets_same_colour {n r : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsCycleCopy H r) (hr : Odd r) (c : Fin n → Fin 2) :
    ∃ u v, H.Adj u v ∧ c u = c v := by
  by_contra h
  apply hH.not_bipartite hr
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro u v huv hc
  exact h ⟨u, v, huv, hc⟩

theorem HasCycleDecomposition.edge_count_le_obstruction {n r : ℕ}
    {G S : SimpleGraph (Fin n)} (hG : HasCycleDecomposition G r) (hr : Odd r)
    (c : Fin n → Fin 2) (hS : S ≤ G)
    (hcolour : ∀ u v, G.Adj u v → c u = c v → S.Adj u v) :
    G.edgeFinset.card ≤ r * S.edgeFinset.card := by
  obtain ⟨q, H, hpart, hH⟩ := hG
  have hcount : G.edgeFinset.card = q * r := by
    rw [hpart.edge_count]
    simp only [fun i => (hH i).edge_card, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hfilter' : G.edgeFinset.filter (fun e => e ∈ S.edgeFinset) = S.edgeFinset := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(SimpleGraph.edgeFinset_mono hS) h, h⟩⟩
  have hsum := hpart.filtered_edge_count (fun e => e ∈ S.edgeFinset)
  rw [hfilter'] at hsum
  have hq : q ≤ S.edgeFinset.card := by
    rw [hsum]
    have h₁ : ∑ _ : Fin q, (1 : ℕ) ≤
        ∑ i : Fin q, ((H i).edgeFinset.filter (fun e => e ∈ S.edgeFinset)).card := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.one_le_card.mpr
      obtain ⟨u, v, huv, hc⟩ := (hH i).meets_same_colour hr c
      refine ⟨s(u, v), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact SimpleGraph.mem_edgeFinset.mpr huv
      · exact SimpleGraph.mem_edgeFinset.mpr
          (hcolour u v (hpart.piece_le i huv) hc)
    simpa using h₁
  rw [hcount]
  nlinarith

end Oberwolfach
