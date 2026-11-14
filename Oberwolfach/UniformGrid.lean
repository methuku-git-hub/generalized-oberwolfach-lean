module

public import Oberwolfach.UniformThreshold

@[expose] public section

/-! Uniformity in the allowed set follows from the fixed-set statement alone.
The finite family consists of sublevel sets of the ordinary cycle thresholds.
No asymptotic estimate in the cycle length is required for this reduction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem allowedThreshold_nonneg {S : Set ℕ} (hS : S.Nonempty) :
    0 ≤ allowedThreshold S := by
  obtain ⟨r, hr⟩ := hS
  apply (cycleThreshold_nonneg r).trans
  apply le_csSup (show BddAbove (cycleThreshold '' S) from ?_) ⟨r, hr, rfl⟩
  refine ⟨1, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact cycleThreshold_le_one s

theorem allowedThreshold_le_one {S : Set ℕ} (hS : S.Nonempty) :
    allowedThreshold S ≤ 1 := by
  apply csSup_le (hS.image cycleThreshold)
  rintro y ⟨r, hr, rfl⟩
  exact cycleThreshold_le_one r

/-- The fixed-set theorem already implies the uniform statement. The hypothesis
is an unproved target, not an axiom or an asserted decomposition result. -/
theorem uniform_of_fixed_set_grid (hfixed : FixedSetTheorem) : MainTheorem := by
  classical
  intro α hα
  have hhalf : 0 < α / 2 := by linarith
  let M : ℕ := ⌈1 / (α / 2)⌉₊
  let T (q : Fin (M + 1)) : Set ℕ :=
    {r | 3 ≤ r ∧ cycleThreshold r ≤ (q.val : ℝ) * (α / 2)}
  have hf : ∀ q : Fin (M + 1), ∃ N : ℕ,
      (T q).Nonempty → ∀ n ≥ N, DecompositionAt (T q) (α / 2) n := by
    intro q
    by_cases hq : (T q).Nonempty
    · obtain ⟨N, hN⟩ := hfixed (T q) hq (fun r hr => hr.1) (α / 2) hhalf
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => (hq h).elim⟩
  choose bound hbound using hf
  refine ⟨Finset.univ.sup bound, ?_⟩
  intro S hSne hS n hn
  let θ := allowedThreshold S
  have hθ0 : 0 ≤ θ := allowedThreshold_nonneg hSne
  have hθ1 : θ ≤ 1 := allowedThreshold_le_one hSne
  let q : Fin (M + 1) := ⟨⌈θ / (α / 2)⌉₊, by
    have : ⌈θ / (α / 2)⌉₊ ≤ M :=
      Nat.ceil_mono (div_le_div_of_nonneg_right hθ1 hhalf.le)
    omega⟩
  have hround_lower : θ ≤ (q.val : ℝ) * (α / 2) := by
    exact (div_le_iff₀ hhalf).mp (Nat.le_ceil (θ / (α / 2)))
  have hround_upper : (q.val : ℝ) * (α / 2) ≤ θ + α / 2 := by
    have hc := Nat.ceil_lt_add_one (div_nonneg hθ0 hhalf.le)
    have := mul_lt_mul_of_pos_right hc hhalf
    dsimp only [q]
    calc
      (⌈θ / (α / 2)⌉₊ : ℝ) * (α / 2) ≤
          (θ / (α / 2) + 1) * (α / 2) := this.le
      _ = θ + α / 2 := by field_simp
  have hST : S ⊆ T q := by
    intro r hr
    refine ⟨hS r hr, ?_⟩
    apply le_trans ?_ hround_lower
    apply le_csSup (show BddAbove (cycleThreshold '' S) from ?_) ⟨r, hr, rfl⟩
    refine ⟨1, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact cycleThreshold_le_one s
  have hTne := hSne.mono hST
  have hTupper : allowedThreshold (T q) ≤ (q.val : ℝ) * (α / 2) := by
    apply csSup_le (hTne.image cycleThreshold)
    rintro y ⟨r, hr, rfl⟩
    exact hr.2
  apply decompositionAt_transfer hST
    (show allowedThreshold (T q) + α / 2 ≤ allowedThreshold S + α by
      dsimp only [θ] at hround_upper
      linarith)
  exact hbound q hTne n ((Finset.le_sup (Finset.mem_univ q)).trans hn)

end Oberwolfach
