module

public import Oberwolfach.SumGraphTools
public import Oberwolfach.ThresholdBounds

@[expose] public section

/-! Dense divisible graphs whose closed component has a nondivisible edge count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def twoComponentGraph (t : ℕ) : SimpleGraph (Fin ((t - 1) + (t + 1))) :=
  disjointSumOnFin (⊤ : SimpleGraph (Fin (t - 1))) (SimpleGraph.cycleGraph (t + 1))ᶜ

theorem twoComponentGraph_regular {t : ℕ} (ht : 2 ≤ t) :
    (twoComponentGraph t).IsRegularOfDegree (t - 2) := by
  apply disjointSumOnFin_regular
  · intro v
    have hh := SimpleGraph.complete_graph_degree v
    have hh' : (⊤ : SimpleGraph (Fin (t - 1))).degree v = t - 1 - 1 := by
      simpa only [SimpleGraph.completeGraph_eq_top, Fintype.card_fin,
        ← SimpleGraph.ncard_neighborSet] using hh
    have he : t - 1 - 1 = t - 2 := by omega
    simpa only [he, ← SimpleGraph.ncard_neighborSet] using hh'
  · intro v
    rw [SimpleGraph.degree_compl, Fintype.card_fin,
      (cycleGraph_regular (by omega : 3 ≤ t + 1)) v]
    omega

theorem twoComponentGraph_edge_card {t : ℕ} (ht : 2 ≤ t) :
    (twoComponentGraph t).edgeFinset.card = t * (t - 2) := by
  have hreg : ∀ v, (twoComponentGraph t).degree v = t - 2 := twoComponentGraph_regular ht
  have hh := (twoComponentGraph t).sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
  have hn : t - 1 + (t + 1) = 2 * t := by omega
  simp only [hn] at hh
  nlinarith

theorem twoComponentGraph_internal_card (t : ℕ) :
    (internalEdges (twoComponentGraph t) (sumLeftVertices (t - 1) (t + 1))).card =
      (t - 1).choose 2 := by
  rw [twoComponentGraph, disjointSumOnFin_internal_left_card]
  simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Fintype.card_fin]
    using (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin (t - 1)))

theorem clique_component_not_divisible {r k : ℕ} (hr : 3 ≤ r) (hk : 1 ≤ k) :
    ¬ r ∣ (2 * r * k - 1).choose 2 := by
  intro hdiv
  obtain ⟨c, hc⟩ := hdiv
  let t := 2 * r * k
  have ht : 2 ≤ t := by dsimp only [t]; nlinarith
  have hchoose : 2 * (t - 1).choose 2 = (t - 1) * (t - 2) := by
    rw [Nat.choose_two_right,
      Nat.mul_div_cancel' (Nat.even_mul_pred_self (t - 1)).two_dvd]
    congr 1
  change (t - 1).choose 2 = r * c at hc
  rw [hc] at hchoose
  have heq : (2 : ℤ) * r * c = ((t : ℤ) - 1) * ((t : ℤ) - 2) := by
    have hh : ((2 * (r * c) : ℕ) : ℤ) =
        (((t - 1) * (t - 2) : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hchoose
    push_cast [Nat.cast_sub (show 1 ≤ t by omega), Nat.cast_sub ht] at hh
    nlinarith
  have htcast : (t : ℤ) = 2 * r * k := by dsimp only [t]; push_cast; ring
  rw [htcast] at heq
  have hdiv2 : (r : ℤ) ∣ 2 := by
    refine ⟨2 * c - 4 * (r : ℤ) * k ^ 2 + 6 * k, ?_⟩
    nlinarith [heq]
  have hr2 : r ∣ 2 := Int.natCast_dvd_natCast.mp hdiv2
  have := Nat.le_of_dvd (by decide : 0 < 2) hr2
  omega

theorem twoComponentGraph_no_decomposition {r k : ℕ} (hr : 3 ≤ r) (hk : 1 ≤ k) :
    ¬ HasCycleDecomposition (twoComponentGraph (2 * r * k)) r := by
  intro hdec
  have hclosed := disjointSumOnFin_closed (⊤ : SimpleGraph (Fin (2 * r * k - 1)))
    (SimpleGraph.cycleGraph (2 * r * k + 1))ᶜ
  have hh := hdec.closed_set_edge_divisible
    (sumLeftVertices (2 * r * k - 1) (2 * r * k + 1)) hclosed
  rw [twoComponentGraph_internal_card] at hh
  exact clique_component_not_divisible hr hk hh

theorem cycle_divisible_dense_counterexample {r : ℕ} (hr : 3 ≤ r)
    {d : ℝ} (hd : d < 1 / 2) (N : ℕ) :
    ∃ n ≥ N, ∃ G : SimpleGraph (Fin n), CycleDivisible G r ∧
      (∀ v, d * (n : ℝ) ≤ (G.degree v : ℝ)) ∧ ¬ HasCycleDecomposition G r := by
  classical
  have hmargin : 0 < 1 - 2 * d := by linarith
  let k := max (N + 1) ⌈2 / (1 - 2 * d)⌉₊
  have hkN : N + 1 ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := by omega
  have hceil : 2 / (1 - 2 * d) ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (N + 1) ⌈2 / (1 - 2 * d)⌉₊))
  let t := 2 * r * k
  have ht : 2 ≤ t := by dsimp only [t]; nlinarith
  have hkt : k ≤ t := by dsimp only [t]; nlinarith
  have hn : t - 1 + (t + 1) = 2 * t := by omega
  have htreal : 2 ≤ (1 - 2 * d) * t := by
    have hh := (div_le_iff₀ hmargin).mp hceil
    have hcast : (k : ℝ) ≤ t := by exact_mod_cast hkt
    nlinarith
  refine ⟨(t - 1) + (t + 1), by omega, twoComponentGraph t, ?_, ?_, ?_⟩
  · constructor
    · intro v
      rw [twoComponentGraph_regular ht v]
      refine ⟨r * k - 1, ?_⟩
      have hprod : 1 ≤ r * k := by nlinarith
      dsimp only [t]
      rw [mul_assoc]
      omega
    · rw [twoComponentGraph_edge_card ht]
      apply dvd_mul_of_dvd_left
      exact ⟨2 * k, by dsimp only [t]; ring⟩
  · intro v
    rw [twoComponentGraph_regular ht v, hn, Nat.cast_sub ht]
    push_cast
    nlinarith
  · exact twoComponentGraph_no_decomposition hr hk1

theorem cycleThreshold_half_le {r : ℕ} (hr : 3 ≤ r) :
    (1 / 2 : ℝ) ≤ cycleThreshold r := by
  classical
  apply le_csInf (show {d | AdmissibleCycleBound r d}.Nonempty from ⟨1, one_admissible r⟩)
  intro d hd
  by_contra hnot
  obtain ⟨N, hN⟩ := hd.2
  obtain ⟨n, hn, G, hdiv, hdeg, hno⟩ :=
    cycle_divisible_dense_counterexample hr (lt_of_not_ge hnot) N
  exact hno (hN n hn G hdiv hdeg)

/-- The fixed-set preparation has density at least one half. -/
theorem allowedThreshold_half_le {S : Set ℕ} (hS : S.Nonempty)
    (hvalid : ∀ r ∈ S, 3 ≤ r) : (1 / 2 : ℝ) ≤ allowedThreshold S := by
  obtain ⟨r, hr⟩ := hS
  apply (cycleThreshold_half_le (hvalid r hr)).trans
  apply le_csSup (show BddAbove (cycleThreshold '' S) from ?_) ⟨r, hr, rfl⟩
  refine ⟨1, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact cycleThreshold_le_one s

end Oberwolfach
