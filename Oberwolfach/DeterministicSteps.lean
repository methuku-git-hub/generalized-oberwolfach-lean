module

public import Mathlib.Tactic

@[expose] public section

/-! Explicit deterministic transfers used inside the cover-down and common-event proofs.
These lemmas do not prove the sampling events themselves. -/
set_option autoImplicit false
namespace Oberwolfach

/-- The local-scale conversion used in both cover-down inductions. -/
theorem local_scale_error {δ C σ ε m n : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hn : 0 ≤ n)
    (hsize : ε * m / 2 ≤ n) (hmargin : 2 * C * σ / ε ≤ δ) :
    δ * n + C * σ * m ≤ 2 * δ * n := by
  have hstep := mul_le_mul_of_nonneg_left hsize (mul_nonneg hC hσ)
  have hb : 2 * C * σ ≤ δ * ε := (div_le_iff₀ hε).mp hmargin
  have hscaled := mul_le_mul_of_nonneg_right hb hn
  have : C * σ * m ≤ δ * n := by nlinarith
  linarith

/-- Scalar calculation in `lem:pr:cut-stability`, using the manuscript's
normalization min(a2*x,a1*y), rather than a product-density normalization.
The graph-theoretic bound on the number of removed edges is an explicit input. -/
theorem large_cut_stability_arithmetic {a1 a2 x y h b original remaining : ℝ}
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hb : 0 ≤ b)
    (hcut : h * min (a2 * x) (a1 * y) ≤ original)
    (hdelete : original - b * min x y ≤ remaining) :
    (h - b / min a1 a2) * min (a2 * x) (a1 * y) ≤ remaining := by
  have hm : 0 < min a1 a2 := lt_min ha1 ha2
  have hscale : min a1 a2 * min x y ≤ min (a2 * x) (a1 * y) := by
    apply le_min
    · exact mul_le_mul (min_le_right _ _) (min_le_left _ _) (le_min hx hy) ha2.le
    · exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_min hx hy) ha1.le
  have hscaled := mul_le_mul_of_nonneg_left hscale (div_nonneg hb hm.le)
  have hid : b / min a1 a2 * (min a1 a2 * min x y) = b * min x y := by
    field_simp
  rw [hid] at hscaled
  nlinarith

/-- Universal estimates on one event remain valid for outcome-dependent choices.
No intersection of separately chosen events occurs in this implication. -/
theorem common_event_adaptive_choice {Ω X : Type*} (E : Set Ω)
    (admissible conclusion : Ω → X → Prop)
    (h : ∀ ω ∈ E, ∀ x, admissible ω x → conclusion ω x)
    (choose : Ω → X) (hc : ∀ ω ∈ E, admissible ω (choose ω)) :
    E ⊆ {ω | conclusion ω (choose ω)} := by
  intro ω hω
  exact h ω hω (choose ω) (hc ω hω)

/-- Exact set identity behind the non-accumulation of deletion errors. -/
theorem protected_restriction {V : Type*} (C E T Next : Set V)
    (hC : C ∩ T = Next) (hE : E ∩ T = ∅) : (C \ E) ∩ T = Next := by
  rw [← hC]
  ext x
  have he : x ∈ E → x ∉ T := by
    intro hx ht
    have : x ∈ E ∩ T := ⟨hx, ht⟩
    rw [hE] at this
    exact this
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  tauto

end Oberwolfach
