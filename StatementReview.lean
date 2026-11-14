module

public import Challenge
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

/-! Independent checks of elementary interpretations of the Challenge.
These lemmas are not used to prove the project theorem. -/

open SimpleGraph
open Oberwolfach

namespace StatementReview

theorem partition_piece_subgraph {n q : ℕ} {G : SimpleGraph (Fin n)}
    {pieces : Fin q → SimpleGraph (Fin n)} (h : EdgePartition G pieces) (i : Fin q) :
    pieces i ≤ G := by
  intro u v huv
  exact (h u v).1.mpr ⟨i, huv⟩

theorem partition_piece_unique {n q : ℕ} {G : SimpleGraph (Fin n)}
    {pieces : Fin q → SimpleGraph (Fin n)} (h : EdgePartition G pieces)
    {u v : Fin n} {i j : Fin q} (hi : (pieces i).Adj u v) (hj : (pieces j).Adj u v) :
    i = j := (h u v).2 i j hi hj

theorem one_is_admissible (r : ℕ) : AdmissibleCycleBound r 1 := by
  classical
  refine ⟨by norm_num, 1, ?_⟩
  intro n hn G _ hmin
  let v : Fin n := ⟨0, by omega⟩
  have hlt : G.degree v < n := by simpa using G.degree_lt_card_verts v
  have hle : (n : ℝ) ≤ G.degree v := by simpa using hmin v
  have hlt' : (G.degree v : ℝ) < (n : ℝ) := by exact_mod_cast hlt
  linarith

theorem threshold_nonnegative (r : ℕ) : 0 ≤ cycleThreshold r := by
  apply le_csInf
  · exact ⟨1, one_is_admissible r⟩
  · intro d hd
    exact hd.1.1

theorem threshold_at_most_one (r : ℕ) : cycleThreshold r ≤ 1 := by
  apply csInf_le
  · exact ⟨0, by intro d hd; exact hd.1.1⟩
  · exact one_is_admissible r

theorem allowed_threshold_nonnegative {S : Set ℕ} (hS : S.Nonempty) :
    0 ≤ allowedThreshold S := by
  obtain ⟨r, hr⟩ := hS
  have hbounded : BddAbove (cycleThreshold '' S) :=
    ⟨1, by rintro _ ⟨r, _, rfl⟩; exact threshold_at_most_one r⟩
  exact (threshold_nonnegative r).trans (le_csSup hbounded ⟨r, hr, rfl⟩)

theorem allowed_threshold_at_most_one {S : Set ℕ} (hS : S.Nonempty) :
    allowedThreshold S ≤ 1 := by
  apply csSup_le
  · obtain ⟨r, hr⟩ := hS
    exact ⟨cycleThreshold r, r, hr, rfl⟩
  · rintro _ ⟨r, _, rfl⟩
    exact threshold_at_most_one r

theorem regular_two_component_is_cycle {n : ℕ} (F : SimpleGraph (Fin n))
    [F.LocallyFinite] (hF : F.IsRegularOfDegree 2) (v : Fin n) :
    ∃ p : F.Walk v v, p.IsCycle ∧
      p.toSubgraph.verts = {w | F.Reachable v w} ∧
      ∀ w ∈ p.toSubgraph.verts, ∀ z, p.toSubgraph.Adj w z ↔ F.Adj w z := by
  classical
  have hcycles : F.IsCycles := by
    intro w _
    rw [F.ncard_neighborSet]
    exact hF w
  have hnonempty : (F.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [F.ncard_neighborSet, hF v]
    decide
  have hv : v ∈ (F.connectedComponentMk v).supp := by
    simp [ConnectedComponent.mem_supp_iff]
  obtain ⟨p, hp, hverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hnonempty
  refine ⟨p, hp, ?_, ?_⟩
  · rw [hverts]
    ext w
    simp [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, reachable_comm]
  · intro w hw z
    exact hp.adj_toSubgraph_iff_of_isCycles hcycles hw z

theorem successor_val_iff {r : ℕ} [NeZero r] (hr : 3 ≤ r) (i j : Fin r) :
    (i.val + 1) % r = j.val ↔ i + 1 = j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ r by omega)
  simp [Fin.ext_iff, Fin.val_add]

theorem cycle_adj_iff_successor {r : ℕ} [NeZero r] (hr : 3 ≤ r) (i j : Fin r) :
    (cycleGraph r).Adj i j ↔ i + 1 = j ∨ j + 1 = i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ r by omega)
  rw [cycleGraph_adj, sub_eq_iff_eq_add, sub_eq_iff_eq_add]
  simp [eq_comm, add_comm, or_comm]

theorem cycle_copy_is_injected_cycle_graph {n r : ℕ} {H : SimpleGraph (Fin n)} :
    IsCycleCopy H r ↔ 3 ≤ r ∧ ∃ f : Fin r ↪ Fin n, ∀ u v,
      H.Adj u v ↔ ∃ i j : Fin r, f i = u ∧ f j = v ∧ (cycleGraph r).Adj i j := by
  constructor
  · rintro ⟨hr, f, hf⟩
    let : NeZero r := ⟨by omega⟩
    refine ⟨hr, f, ?_⟩
    intro u v
    rw [hf u v]
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    rw [cycle_adj_iff_successor hr, ← successor_val_iff hr, ← successor_val_iff hr]
  · rintro ⟨hr, f, hf⟩
    let : NeZero r := ⟨by omega⟩
    refine ⟨hr, f, ?_⟩
    intro u v
    rw [hf u v]
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    rw [cycle_adj_iff_successor hr, ← successor_val_iff hr, ← successor_val_iff hr]

end StatementReview

#print axioms StatementReview.partition_piece_subgraph
#print axioms StatementReview.partition_piece_unique
#print axioms StatementReview.one_is_admissible
#print axioms StatementReview.threshold_nonnegative
#print axioms StatementReview.threshold_at_most_one
#print axioms StatementReview.allowed_threshold_nonnegative
#print axioms StatementReview.allowed_threshold_at_most_one
#print axioms StatementReview.regular_two_component_is_cycle

#print axioms StatementReview.cycle_copy_is_injected_cycle_graph
