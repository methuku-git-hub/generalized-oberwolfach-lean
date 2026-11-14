module

public import Oberwolfach.SumGraphTools
public import Oberwolfach.OddCycleEdgeCount
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

@[expose] public section

/-! Two equal parts, retaining an internal regular graph in each part and all
edges between the parts. This supplies explicit odd-cycle obstruction graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def twoPartJoin {t : ℕ} (H : SimpleGraph (Fin t)) : SimpleGraph (Fin (t + t)) :=
  (disjointSumOnFin Hᶜ Hᶜ)ᶜ

def twoPartColour {t : ℕ} (v : Fin (t + t)) : Fin 2 :=
  Sum.elim (fun _ => 0) (fun _ => 1)
    ((finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).symm v)

theorem twoPartJoin_adj {t : ℕ} (H : SimpleGraph (Fin t)) (u v : Fin t ⊕ Fin t) :
    (twoPartJoin H).Adj (finSumFinEquiv u) (finSumFinEquiv v) ↔
      u ≠ v ∧ ¬ (Hᶜ.sum Hᶜ).Adj u v := by
  rw [twoPartJoin, SimpleGraph.compl_adj, disjointSumOnFin_adj]
  exact and_congr_left (fun _ => not_congr finSumFinEquiv.injective.eq_iff)

theorem internal_sum_le_twoPartJoin {t : ℕ} (H : SimpleGraph (Fin t)) :
    disjointSumOnFin H H ≤ twoPartJoin H := by
  intro u v huv
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective u
  obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective v
  rw [disjointSumOnFin_adj] at huv
  rw [twoPartJoin_adj]
  cases u <;> cases v <;> simp only [SimpleGraph.sum_adj] at huv ⊢
  · exact ⟨fun h => huv.ne (Sum.inl.inj h), fun h => h.2 huv⟩
  · exact ⟨fun h => huv.ne (Sum.inr.inj h), fun h => h.2 huv⟩

theorem twoPartJoin_same_colour {t : ℕ} (H : SimpleGraph (Fin t))
    (u v : Fin (t + t)) (huv : (twoPartJoin H).Adj u v)
    (hc : twoPartColour u = twoPartColour v) :
    (disjointSumOnFin H H).Adj u v := by
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective u
  obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective v
  rw [twoPartJoin_adj] at huv
  rw [disjointSumOnFin_adj]
  simp only [twoPartColour, Equiv.symm_apply_apply] at hc
  cases u <;> cases v <;> simp only [SimpleGraph.sum_adj, Sum.elim_inl, Sum.elim_inr] at *
  · by_contra h
    exact huv.2 ⟨fun he => huv.1 (congrArg Sum.inl he), h⟩
  · exact (by norm_num at hc)
  · exact (by norm_num at hc)
  · by_contra h
    exact huv.2 ⟨fun he => huv.1 (congrArg Sum.inr he), h⟩

theorem twoPartJoin_regular {t q : ℕ} (H : SimpleGraph (Fin t))
    (ht : 0 < t) (hH : H.IsRegularOfDegree q) :
    (twoPartJoin H).IsRegularOfDegree (t + q) := by
  have hq : q < t := by
    have hh := H.degree_lt_card_verts (⟨0, ht⟩ : Fin t)
    rw [hH _, Fintype.card_fin] at hh
    exact hh
  have hsum := disjointSumOnFin_regular Hᶜ Hᶜ
    (d := t - 1 - q)
    (by intro v; simpa only [← SimpleGraph.ncard_neighborSet, Fintype.card_fin] using hH.compl v)
    (by intro v; simpa only [← SimpleGraph.ncard_neighborSet, Fintype.card_fin] using hH.compl v)
  have heq : t + t - 1 - (t - 1 - q) = t + q := by omega
  intro v
  simpa only [Fintype.card_fin, heq, twoPartJoin, ← SimpleGraph.ncard_neighborSet] using hsum.compl v

theorem regular_graph_even_order_edges {t q : ℕ} {G : SimpleGraph (Fin (t + t))}
    (hG : G.IsRegularOfDegree q) : G.edgeFinset.card = t * q := by
  have hh := G.sum_degrees_eq_twice_card_edges
  have hdegree : ∀ v, G.degree v = q := hG
  simp only [hdegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
  nlinarith

theorem twoPartJoin_no_odd_decomposition {t q r : ℕ} (H : SimpleGraph (Fin t))
    (ht : 0 < t) (hH : H.IsRegularOfDegree q) (hr : Odd r)
    (hgap : r * q < t + q) :
    ¬ HasCycleDecomposition (twoPartJoin H) r := by
  intro hdec
  have hh := hdec.edge_count_le_obstruction hr twoPartColour
    (internal_sum_le_twoPartJoin H) (twoPartJoin_same_colour H)
  rw [regular_graph_even_order_edges (twoPartJoin_regular H ht hH),
    regular_graph_even_order_edges (disjointSumOnFin_regular H H hH hH)] at hh
  nlinarith

def cliqueUnionOnFin (a s : ℕ) : SimpleGraph (Fin (a * s)) :=
  ((SimpleGraph.completeEquipartiteGraph a s).map
    (finProdFinEquiv : Fin a × Fin s ≃ Fin (a * s)).toEmbedding)ᶜ

theorem cliqueUnionOnFin_regular {a s : ℕ} (ha : 0 < a) (hs : 0 < s) :
    (cliqueUnionOnFin a s).IsRegularOfDegree (s - 1) := by
  have hbase : ((SimpleGraph.completeEquipartiteGraph a s).map
      (finProdFinEquiv : Fin a × Fin s ≃ Fin (a * s)).toEmbedding).IsRegularOfDegree
      ((a - 1) * s) := by
    intro x
    let e : Fin a × Fin s ≃ Fin (a * s) := finProdFinEquiv
    obtain ⟨y, rfl⟩ := e.surjective x
    have hh := SimpleGraph.degree_map_apply (SimpleGraph.completeEquipartiteGraph a s)
      e.toEmbedding y
    rw [SimpleGraph.degree_completeEquipartiteGraph] at hh
    simpa only [e, ← SimpleGraph.ncard_neighborSet, Equiv.toEmbedding_apply] using hh
  have hcomp := hbase.compl
  have heq : a * s - 1 - (a - 1) * s = s - 1 := by
    have ha' : a = (a - 1) + 1 := by omega
    have hm : a * s = (a - 1) * s + s := calc
      a * s = ((a - 1) + 1) * s := congrArg (fun z => z * s) ha'
      _ = _ := by ring
    omega
  intro v
  simpa only [cliqueUnionOnFin, Fintype.card_fin, heq, ← SimpleGraph.ncard_neighborSet] using hcomp v

end Oberwolfach
