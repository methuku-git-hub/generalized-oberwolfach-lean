module

public import Oberwolfach.TwoPartJoin
public import Oberwolfach.ThresholdBounds

@[expose] public section

/-! Sharp ordinary odd-cycle lower bounds, from explicit regular graphs.
The internal regular graph is a union of equal cliques; this avoids any
unproved regular-graph existence input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem odd_threshold_counterexample {r : ℕ} (hr3 : 3 ≤ r) (hr : Odd r)
    {d : ℝ} (hd : d < (r : ℝ) / (2 * r - 2)) (N : ℕ) :
    ∃ n ≥ N, ∃ G : SimpleGraph (Fin n), CycleDivisible G r ∧
      (∀ v, d * (n : ℝ) ≤ (G.degree v : ℝ)) ∧ ¬ HasCycleDecomposition G r := by
  classical
  have hrreal : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have hden : (0 : ℝ) < 2 * r - 2 := by linarith
  have hd' := (lt_div_iff₀ hden).mp hd
  let margin : ℝ := r - 2 * d * (r - 1)
  have hm : 0 < margin := by dsimp only [margin]; nlinarith
  let k := max (N + 1) ⌈1 / margin⌉₊
  let s := r * (2 * k + 1)
  let t := (r - 1) * s
  let H := cliqueUnionOnFin (r - 1) s
  have hkN : N + 1 ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := by omega
  have hs : 0 < s := by dsimp only [s]; positivity
  have ht : 0 < t := by dsimp only [t]; exact Nat.mul_pos (by omega) hs
  have hks : k ≤ s := by dsimp only [s]; nlinarith
  have hst : s ≤ t := by dsimp only [t]; nlinarith [show 1 ≤ r - 1 by omega]
  have hceil : 1 / margin ≤ (s : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (show ⌈1 / margin⌉₊ ≤ s from (le_max_right _ _).trans hks))
  have hmargin : 1 ≤ margin * s := by
    have hh := (div_le_iff₀ hm).mp hceil
    nlinarith
  have hH : H.IsRegularOfDegree (s - 1) := cliqueUnionOnFin_regular (by omega) hs
  have hG := twoPartJoin_regular H ht hH
  have hrsub : r - 1 + 1 = r := by omega
  have hnat : t + s = r * s := by
    dsimp only [t]
    calc
      (r - 1) * s + s = (r - 1 + 1) * s := by ring
      _ = r * s := by rw [hrsub]
  have hgap : r * (s - 1) < t + (s - 1) := by
    have hs' : s - 1 + 1 = s := by omega
    have hmul : r * (s - 1) + r = r * s := by
      calc
        r * (s - 1) + r = r * (s - 1 + 1) := by ring
        _ = r * s := by rw [hs']
    omega
  refine ⟨t + t, by omega, twoPartJoin H, ?_, ?_, ?_⟩
  · constructor
    · intro v
      rw [hG v]
      have hteven : Even t := (hr.tsub_odd (by decide : Odd 1)).mul_right s
      have hsodd : Odd s := hr.mul ⟨k, rfl⟩
      exact hteven.add (hsodd.tsub_odd (by decide : Odd 1))
    · rw [regular_graph_even_order_edges hG]
      apply dvd_mul_of_dvd_left
      refine ⟨(r - 1) * (2 * k + 1), ?_⟩
      dsimp only [t, s]
      ring
  · intro v
    rw [hG v]
    have htcast : (t : ℝ) = ((r : ℝ) - 1) * s := by
      dsimp only [t]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    dsimp only [margin] at hmargin
    nlinarith
  · exact twoPartJoin_no_odd_decomposition H ht hH hr hgap

theorem cycleThreshold_odd_sharp_lower {r : ℕ} (hr3 : 3 ≤ r) (hr : Odd r) :
    (r : ℝ) / (2 * r - 2) ≤ cycleThreshold r := by
  apply le_csInf (show {d | AdmissibleCycleBound r d}.Nonempty from ⟨1, one_admissible r⟩)
  intro d hd
  by_contra hnot
  obtain ⟨N, hN⟩ := hd.2
  obtain ⟨n, hn, G, hdiv, hdegree, hno⟩ :=
    odd_threshold_counterexample hr3 hr (lt_of_not_ge hnot) N
  exact hno (hN n hn G hdiv hdegree)

theorem cycleThreshold_triangle_lower : (3 / 4 : ℝ) ≤ cycleThreshold 3 := by
  convert cycleThreshold_odd_sharp_lower (by decide : 3 ≤ 3) (by decide : Odd 3) using 1
  norm_num

end Oberwolfach
