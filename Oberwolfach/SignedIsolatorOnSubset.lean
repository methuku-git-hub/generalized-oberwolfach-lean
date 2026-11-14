module

public import Oberwolfach.FractionalEdgeDeletion

@[expose] public section

/-! Signed edge isolation on an induced vertex set, with weights interpreted
on the original physical graph. Vertices outside the set have zero load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem signed_cycle_edge_isolator_on_subset (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],∀ (G : SimpleGraph V) (S : Finset V),
      N≤S.card →
      (∀ z∈S,(cycleThreshold r+α)*S.card≤((G.neighborFinset z∩S).card:ℝ)) →
      ∀ u v,u∈S → v∈S → G.Adj u v →
      ∃ I : SimpleGraph V → ℝ,
        (∀ C,I C≠0 → C≤spanningRestriction G S ∧ IsEmbeddedCycle C r) ∧
        (∀ C,|I C|≤1) ∧
        (∀ x y,(∑ C,if C.Adj x y then I C else 0)=
          if (SimpleGraph.edge u v).Adj x y then 1 else 0) ∧
        (∀ x,(∑ C,if x∈C.support then I C else 0)=
          (1/2:ℝ)*(if x=u ∨ x=v then 1 else 0)) := by
  obtain ⟨N,hN⟩ := fractional_cycle_edge_deletion r hr α hα
  refine ⟨N,?_⟩
  intro V _ _ G S hS hdeg u v hu hv huv
  let uS : (S:Set V) := ⟨u,hu⟩
  let vS : (S:Set V) := ⟨v,hv⟩
  obtain ⟨hB,hD⟩ := hN (S:Set V) (by simpa using hS) (G.induce (S:Set V)) (by
    intro z
    have he := induced_degree_intersection G S z
    simp only [← SimpleGraph.ncard_neighborSet] at he ⊢
    rw [he]
    simpa only [Fintype.card_coe,Finset.coe_sort_coe] using hdeg z.val z.property)
  have hB' := hB.map_embedded_cycles (Function.Embedding.subtype (S:Set V))
  have hD' := (hD uS vS huv).map_embedded_cycles (Function.Embedding.subtype (S:Set V))
  rw [graph_map_delete_edge] at hD'
  change HasFractionalDecomposition (spanningRestriction G S\SimpleGraph.edge u v)
    (fun C => IsEmbeddedCycle C r) at hD'
  have huvs : (spanningRestriction G S).Adj u v :=
    (spanningRestriction_adj G S u v).mpr ⟨huv,hu,hv⟩
  obtain ⟨I,hs,hb,he,hvtx⟩ := signed_cycle_edge_isolator_of_fractional
    (spanningRestriction G S) u v huvs hB' hD'
  refine ⟨I,hs,hb,he,?_⟩
  intro x
  calc
    _ = ∑ C : SimpleGraph V,if C.degree x≠0 then I C else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      have hc : (x∈C.support) ↔ C.degree x≠0 :=
        (C.degree_pos_iff_mem_support x).symm.trans Nat.pos_iff_ne_zero
      simp only [hc]
    _ = _ := hvtx x

end Oberwolfach
