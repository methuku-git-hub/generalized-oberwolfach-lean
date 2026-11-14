module

public import Oberwolfach.CycleCopies
public import Oberwolfach.ThresholdBounds
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Complete bipartite counterexamples give the half-density lower bound
for every odd cycle length, with divisibility and arbitrarily large order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartite_no_odd_decomposition {n r : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.IsBipartite) (hr : Odd r) {u v : Fin n} (huv : G.Adj u v) :
    ¬ HasCycleDecomposition G r := by
  rintro ⟨q, H, hpart, hH⟩
  obtain ⟨i, hi⟩ := (hpart u v).1.mp huv
  have hsub : H i ≤ G := by
    intro x y hxy
    exact (hpart x y).1.mpr ⟨i, hxy⟩
  exact (hH i).not_bipartite hr (SimpleGraph.Colorable.mono_left hsub hG)

def balancedCompleteBipartite (t : ℕ) : SimpleGraph (Fin (2 * t)) :=
  (SimpleGraph.completeEquipartiteGraph 2 t).map
    (finProdFinEquiv : Fin 2 × Fin t ≃ Fin (2 * t)).toEmbedding

theorem balancedCompleteBipartite_regular (t : ℕ) :
    (balancedCompleteBipartite t).IsRegularOfDegree t := by
  classical
  intro x
  let e : Fin 2 × Fin t ≃ Fin (2 * t) := finProdFinEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  have hh := SimpleGraph.degree_map_apply (SimpleGraph.completeEquipartiteGraph 2 t)
    e.toEmbedding y
  rw [SimpleGraph.degree_completeEquipartiteGraph] at hh
  simpa only [balancedCompleteBipartite, e, ← SimpleGraph.ncard_neighborSet, Equiv.toEmbedding_apply,
    Nat.reduceSub, one_mul] using hh

theorem balancedCompleteBipartite_edge_card (t : ℕ) :
    (balancedCompleteBipartite t).edgeFinset.card = t ^ 2 := by
  classical
  have hh := SimpleGraph.card_edgeFinset_map
    (finProdFinEquiv : Fin 2 × Fin t ≃ Fin (2 * t)).toEmbedding
    (SimpleGraph.completeEquipartiteGraph 2 t)
  rw [SimpleGraph.card_edgeFinset_completeEquipartiteGraph] at hh
  simpa only [balancedCompleteBipartite, ← Set.ncard_coe_finset,
    SimpleGraph.coe_edgeFinset, Nat.choose_self, one_mul] using hh

theorem balancedCompleteBipartite_bipartite (t : ℕ) :
    (balancedCompleteBipartite t).IsBipartite :=
  SimpleGraph.Colorable.map _ SimpleGraph.completeEquipartiteGraph_colorable

theorem balancedCompleteBipartite_has_edge {t : ℕ} (ht : 0 < t) :
    ∃ u v, (balancedCompleteBipartite t).Adj u v := by
  let e : Fin 2 × Fin t ≃ Fin (2 * t) := finProdFinEquiv
  let a : Fin t := ⟨0, ht⟩
  refine ⟨e (0, a), e (1, a), ?_⟩
  apply SimpleGraph.map_adj_apply.mpr
  change (0 : Fin 2) ≠ 1
  decide

theorem odd_cycle_divisible_counterexample {r : ℕ} (hr3 : 3 ≤ r) (hr : Odd r)
    (N : ℕ) :
    ∃ n ≥ N, ∃ G : SimpleGraph (Fin n), CycleDivisible G r ∧
      (∀ v, (n : ℝ) / 2 = (G.degree v : ℝ)) ∧ ¬ HasCycleDecomposition G r := by
  classical
  let t := 2 * r * (N + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨2 * t, ?_, balancedCompleteBipartite t, ?_, ?_, ?_⟩
  · dsimp only [t]
    nlinarith
  · constructor
    · intro v
      rw [balancedCompleteBipartite_regular t v]
      exact ⟨r * (N + 1), by dsimp only [t]; ring⟩
    · rw [balancedCompleteBipartite_edge_card]
      exact ⟨4 * r * (N + 1) ^ 2, by dsimp only [t]; ring⟩
  · intro v
    rw [balancedCompleteBipartite_regular t v]
    push_cast
    ring
  · obtain ⟨u, v, huv⟩ := balancedCompleteBipartite_has_edge ht
    exact bipartite_no_odd_decomposition (balancedCompleteBipartite_bipartite t) hr huv

theorem cycleThreshold_half_le_of_odd {r : ℕ} (hr3 : 3 ≤ r) (hr : Odd r) :
    (1 / 2 : ℝ) ≤ cycleThreshold r := by
  classical
  apply le_csInf (show {d | AdmissibleCycleBound r d}.Nonempty from ⟨1, one_admissible r⟩)
  intro d hd
  by_contra hnot
  have hdlt : d < 1 / 2 := lt_of_not_ge hnot
  obtain ⟨N, hN⟩ := hd.2
  obtain ⟨n, hn, G, hdiv, hdegree, hno⟩ := odd_cycle_divisible_counterexample hr3 hr N
  apply hno (hN n hn G hdiv ?_)
  intro v
  rw [← hdegree v]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Oberwolfach
