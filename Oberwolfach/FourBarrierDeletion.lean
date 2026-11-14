module

public import Oberwolfach.FourBarrierBase
public import Oberwolfach.GraphDeletion

@[expose] public section

/-! Deleting one six-cycle in the third part adjusts edge divisibility while
preserving even degrees and all edges in the first part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fourBarrierSixEmbedding {t : ℕ} (ht : 6 ≤ t) :
    Fin 6 ↪ Fin ((t + t) + (t - 1)) :=
  (Fin.castLEEmb ht).trans (fourBarrierC t)

def fourBarrierSixCycle {t : ℕ} (ht : 6 ≤ t) :
    SimpleGraph (Fin ((t + t) + (t - 1))) :=
  (SimpleGraph.cycleGraph 6).map (fourBarrierSixEmbedding ht)

def fourBarrierGraph {t : ℕ} (ht : 6 ≤ t) :
    SimpleGraph (Fin ((t + t) + (t - 1))) :=
  fourBarrierBase t \ fourBarrierSixCycle ht

theorem fourBarrierSixCycle_le {t : ℕ} (ht : 6 ≤ t) :
    fourBarrierSixCycle ht ≤ fourBarrierBase t := by
  apply SimpleGraph.map_le_iff_le_comap.mpr
  intro u v huv
  change (fourBarrierBase t).Adj
    (fourBarrierC t (Fin.castLEEmb ht u)) (fourBarrierC t (Fin.castLEEmb ht v))
  exact (fourBarrierBase_adj_C _ _ _).mpr ((Fin.castLEEmb ht).injective.ne huv.ne)

theorem fourBarrierSixCycle_card {t : ℕ} (ht : 6 ≤ t) :
    (fourBarrierSixCycle ht).edgeFinset.card = 6 := by
  have hh := SimpleGraph.card_edgeFinset_map (fourBarrierSixEmbedding ht) (SimpleGraph.cycleGraph 6)
  have hc := cycleGraph_edge_card (by decide : 3 ≤ 6)
  simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at hh hc
  simpa only [fourBarrierSixCycle, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    using hh.trans hc

theorem fourBarrierSixCycle_degree {t : ℕ} (ht : 6 ≤ t)
    (x : Fin ((t + t) + (t - 1))) :
    (fourBarrierSixCycle ht).degree x = 0 ∨ (fourBarrierSixCycle ht).degree x = 2 := by
  have hh := mapped_regular_degree_or_zero (SimpleGraph.cycleGraph 6)
    (d := 2)
    (by intro v; simpa only [← SimpleGraph.ncard_neighborSet] using cycleGraph_regular (by decide : 3 ≤ 6) v)
    (fourBarrierSixEmbedding ht) x
  simpa only [fourBarrierSixCycle, ← SimpleGraph.ncard_neighborSet] using hh

theorem fourBarrierGraph_degrees {t : ℕ} (ht : 6 ≤ t)
    (x : Fin ((t + t) + (t - 1))) :
    Even ((fourBarrierGraph ht).degree x) ∧
      2 * t - 4 ≤ (fourBarrierGraph ht).degree x := by
  have hbase := fourBarrierBase_degrees t x
  have hdel := fourBarrierSixCycle_degree ht x
  have hdeg := graph_degree_sdiff (fourBarrierBase t) (fourBarrierSixCycle ht)
    (fourBarrierSixCycle_le ht) x
  have hdeg' : (fourBarrierGraph ht).degree x =
      (fourBarrierBase t).degree x - (fourBarrierSixCycle ht).degree x := by
    simpa only [fourBarrierGraph, ← SimpleGraph.ncard_neighborSet] using hdeg
  rw [hdeg']
  rcases hdel with h | h
  · rw [h, Nat.sub_zero]
    exact ⟨hbase.1, by omega⟩
  · rw [h]
    exact ⟨hbase.1.tsub (by decide : Even 2), by omega⟩

theorem fourBarrierGraph_edge_card {t : ℕ} (ht : 6 ≤ t) :
    (fourBarrierGraph ht).edgeFinset.card = 3 * t * (t - 1) - 6 := by
  have hh := graph_edge_count_sdiff (fourBarrierBase t) (fourBarrierSixCycle ht)
    (fourBarrierSixCycle_le ht)
  rw [fourBarrierBase_edge_card, fourBarrierSixCycle_card] at hh
  simpa only [fourBarrierGraph, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] using hh

theorem fourBarrierGraph_internal_edges {t : ℕ} (ht : 6 ≤ t) :
    (fourBarrierGraph ht).edgeFinset.filter (colourInternalEdge (fourBarrierColour t)) =
      (fourBarrierBase t).edgeFinset.filter (colourInternalEdge (fourBarrierColour t)) := by
  have hh := graph_filtered_edges_sdiff (fourBarrierBase t) (fourBarrierSixCycle ht)
    (colourInternalEdge (fourBarrierColour t)) (by
      intro e he hp hdel
      induction e using Sym2.ind with
      | _ u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hdel
        rw [colourInternalEdge_pair] at hp
        change ((SimpleGraph.cycleGraph 6).map (fourBarrierSixEmbedding ht)).Adj u v at hdel
        rw [SimpleGraph.map_adj] at hdel
        obtain ⟨a, b, hab, rfl, rfl⟩ := hdel
        have hc : fourBarrierColour t (fourBarrierSixEmbedding ht a) = 2 :=
          fourBarrierColour_C t (Fin.castLEEmb ht a)
        rw [hc] at hp
        norm_num at hp)
  ext e
  have hh' := Finset.ext_iff.mp hh e
  simpa only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, fourBarrierGraph] using hh'

theorem fourBarrierGraph_no_decomposition {t : ℕ} (ht : 6 ≤ t)
    (hodd : Odd (t.choose 2)) :
    ¬ HasCycleDecomposition (fourBarrierGraph ht) 4 := by
  intro hdec
  have hallowed : ∀ u v, (fourBarrierGraph ht).Adj u v →
      fourBarrierAllowed (fourBarrierColour t u) (fourBarrierColour t v) := by
    intro u v huv
    exact fourBarrierBase_allowed t u v huv.1
  have hh := hdec.four_internal_even (fourBarrierColour t) hallowed
  rw [fourBarrierGraph_internal_edges, fourBarrierBase_internal_card] at hh
  exact (Nat.not_even_iff_odd.mpr hodd) hh

end Oberwolfach
