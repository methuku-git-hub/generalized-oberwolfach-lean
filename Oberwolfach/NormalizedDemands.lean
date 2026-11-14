module

public import Oberwolfach.PrescribedDegrees

@[expose] public section

/-!
The numerical cut argument in `lem:prelim:normalized-demands`, followed
by its integral existence conclusion. The total demand and both original
part sizes are kept fixed throughout the argument.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- A positive demand deficit forces a cut into the range of the
large-cut hypothesis. Only upper bounds on individual demands are needed
for this implication. -/
theorem normalizedDemand_cut
    {δ δ₀ M C s t Fₛ Fₜ e : ℝ}
    (hδ : 0 ≤ δ) (hδ₀ : δ ≤ δ₀) (hδsmall : δ₀ < 1 / 4)
    (hM : 0 ≤ M) (hMC : 2 * M ≤ C)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hFs : Fₛ ≤ M) (hFt : Fₜ ≤ M)
    (hFsbound : Fₛ ≤ (1 + δ) * M * s)
    (hFtbound : Fₜ ≤ (1 + δ) * M * t)
    (he : 0 ≤ e)
    (hlarge : 1 - 2 * δ₀ < s + t → C * min s t ≤ e) :
    Fₛ + Fₜ - M ≤ e := by
  by_cases hpos : 0 < Fₛ + Fₜ - M
  · have hMpos : 0 < M := by linarith
    have hlarge' : 1 - 2 * δ₀ < s + t := by
      by_contra h
      have hst : s + t ≤ 1 - 2 * δ₀ := le_of_not_gt h
      have hcoef : (1 + δ) * (1 - 2 * δ₀) ≤ 1 := by
        nlinarith [mul_nonneg hδ (le_trans hδ hδ₀)]
      have hscale := mul_le_mul_of_nonneg_left hst
        (mul_nonneg (by linarith : 0 ≤ 1 + δ) hM)
      have hscale' := mul_le_mul_of_nonneg_left hcoef hM
      nlinarith
    have hcoeff : (1 + δ) * M ≤ C := by nlinarith
    have hmin : Fₛ + Fₜ - M ≤ (1 + δ) * M * min s t := by
      rcases le_total s t with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    have hbound := mul_le_mul_of_nonneg_right hcoeff (le_min hs ht)
    exact hmin.trans (hbound.trans (hlarge hlarge'))
  · exact (le_of_not_gt hpos).trans he

/-- Cut inequalities under the manuscript's normalized cut hypothesis.
The two part sizes are positive and the demands have the same fixed total.
This is the integral conclusion used by the deletion-subgraph callers. -/
theorem nearUniform_cutCondition
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    {δ δ₀ M h : ℝ}
    (ha : 0 < Fintype.card X) (hb : 0 < Fintype.card Y)
    (hδ : 0 ≤ δ) (hδ₀ : δ ≤ δ₀) (hδsmall : δ₀ < 1 / 4)
    (hM : 0 ≤ M)
    (hMC : M ≤ h * Fintype.card X * Fintype.card Y / 2)
    (hftotal : ∑ x, (f x : ℝ) = M) (hgtotal : ∑ y, (g y : ℝ) = M)
    (hf : ∀ x, (f x : ℝ) ≤ (1 + δ) * M / Fintype.card X)
    (hg : ∀ y, (g y : ℝ) ≤ (1 + δ) * M / Fintype.card Y)
    (hlarge : ∀ (S : Finset X) (T : Finset Y),
      1 - 2 * δ₀ < (S.card : ℝ) / Fintype.card X + (T.card : ℝ) / Fintype.card Y →
      h * Fintype.card X * Fintype.card Y *
          min ((S.card : ℝ) / Fintype.card X) ((T.card : ℝ) / Fintype.card Y) ≤
        ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ T)).card : ℝ)) :
    ∀ (S : Finset X) (T : Finset Y),
      ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
        (Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∉ T)).card := by
  classical
  intro S T
  let U := Tᶜ
  have hFs : ∑ x ∈ S, (f x : ℝ) ≤ M := by
    rw [← hftotal]
    exact Finset.sum_le_univ_sum_of_nonneg (fun x => Nat.cast_nonneg (f x))
  have hFt : ∑ y ∈ U, (g y : ℝ) ≤ M := by
    rw [← hgtotal]
    exact Finset.sum_le_univ_sum_of_nonneg (fun y => Nat.cast_nonneg (g y))
  have hFsbound : ∑ x ∈ S, (f x : ℝ) ≤
      (1 + δ) * M * ((S.card : ℝ) / Fintype.card X) := by
    calc
      _ ≤ ∑ _ ∈ S, (1 + δ) * M / Fintype.card X :=
        Finset.sum_le_sum (fun x _ => hf x)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hFtbound : ∑ y ∈ U, (g y : ℝ) ≤
      (1 + δ) * M * ((U.card : ℝ) / Fintype.card Y) := by
    calc
      _ ≤ ∑ _ ∈ U, (1 + δ) * M / Fintype.card Y :=
        Finset.sum_le_sum (fun y _ => hg y)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hc := normalizedDemand_cut hδ hδ₀ hδsmall hM
    (show 2 * M ≤ h * Fintype.card X * Fintype.card Y by linarith)
    (div_nonneg (Nat.cast_nonneg S.card) (Nat.cast_pos.mpr ha).le)
    (div_nonneg (Nat.cast_nonneg U.card) (Nat.cast_pos.mpr hb).le)
    hFs hFt hFsbound hFtbound
    (Nat.cast_nonneg (Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ U)).card)
    (hlarge S U)
  have hsum : (∑ y ∈ T, (g y : ℝ)) + (∑ y ∈ U, (g y : ℝ)) = M := by
    rw [show U = Tᶜ from rfl, Finset.sum_add_sum_compl, hgtotal]
  have he : Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ U) =
      Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∉ T) := by
    ext e
    simp [U]
  rw [he] at hc
  have hreal : (∑ x ∈ S, (f x : ℝ)) ≤ (∑ y ∈ T, (g y : ℝ)) +
      ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∉ T)).card : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- The integral existence conclusion of the normalized-demand lemma. -/
theorem bipartite_nearUniformDegrees
    {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    {δ δ₀ M h : ℝ}
    (ha : 0 < Fintype.card X) (hb : 0 < Fintype.card Y)
    (hδ : 0 ≤ δ) (hδ₀ : δ ≤ δ₀) (hδsmall : δ₀ < 1 / 4)
    (hM : 0 ≤ M)
    (hMC : M ≤ h * Fintype.card X * Fintype.card Y / 2)
    (hftotal : ∑ x, (f x : ℝ) = M) (hgtotal : ∑ y, (g y : ℝ) = M)
    (hf : ∀ x, (f x : ℝ) ≤ (1 + δ) * M / Fintype.card X)
    (hg : ∀ y, (g y : ℝ) ≤ (1 + δ) * M / Fintype.card Y)
    (hlarge : ∀ (S : Finset X) (T : Finset Y),
      1 - 2 * δ₀ < (S.card : ℝ) / Fintype.card X + (T.card : ℝ) / Fintype.card Y →
      h * Fintype.card X * Fintype.card Y *
          min ((S.card : ℝ) / Fintype.card X) ((T.card : ℝ) / Fintype.card Y) ≤
        ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ T)).card : ℝ)) :
    ∃ H : Finset E,
      (∀ x, (H.filter (fun e => tail e = x)).card = f x) ∧
      (∀ y, (H.filter (fun e => head e = y)).card = g y) := by
  classical
  have htotal : ∑ x, f x = ∑ y, g y := by
    exact_mod_cast hftotal.trans hgtotal.symm
  exact bipartite_prescribedDegrees tail head f g htotal
    (nearUniform_cutCondition tail head f g ha hb hδ hδ₀ hδsmall hM hMC
      hftotal hgtotal hf hg hlarge)

/-- The same normalized cut argument for a matrix of available edge
multiplicities. This is the form used after deleting protected arcs. -/
theorem nearUniformMultiplicity_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : V → V → ℕ) (f g : V → ℕ) {δ M h : ℝ}
    (hn : 0 < Fintype.card V) (hδ : 0 ≤ δ) (hδsmall : δ < 1 / 4)
    (hM : 0 ≤ M) (hMC : M ≤ h * Fintype.card V * Fintype.card V / 2)
    (hftotal : ∑ x, (f x : ℝ) = M) (hgtotal : ∑ y, (g y : ℝ) = M)
    (hf : ∀ x, (f x : ℝ) ≤ (1 + δ) * M / Fintype.card V)
    (hg : ∀ y, (g y : ℝ) ≤ (1 + δ) * M / Fintype.card V)
    (hlarge : ∀ (S T : Finset V),
      1 - 2 * δ < (S.card : ℝ) / Fintype.card V + (T.card : ℝ) / Fintype.card V →
      h * Fintype.card V * Fintype.card V *
          min ((S.card : ℝ) / Fintype.card V) ((T.card : ℝ) / Fintype.card V) ≤
        ((∑ x, ∑ y, if x ∈ S ∧ y ∈ T then L x y else 0 : ℕ) : ℝ)) :
    ∀ (S T : Finset V), ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
      ∑ x, ∑ y, if x ∈ S ∧ y ∉ T then L x y else 0 := by
  classical
  have hc := nearUniform_cutCondition
    (fun e : BipartiteEdges L => e.1) (fun e => e.2.1) f g
    hn hn hδ (le_refl δ) hδsmall hM hMC hftotal hgtotal hf hg
    (fun S T ht => by
      rw [bipartiteEdges_filter_card L (fun x y => x ∈ S ∧ y ∈ T)]
      exact hlarge S T ht)
  intro S T
  have hs := hc S T
  rw [bipartiteEdges_filter_card L (fun x y => x ∈ S ∧ y ∉ T)] at hs
  exact hs

/-- Demands in `[q-e,q+e]` satisfy the normalized cut criterion with
relative error `2e/(q-e)`. Here `e` is real, as is the error `5 n^(4/5)`
in the protected-partition proof; it is not rounded or assumed integral. -/
theorem intervalDemands_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : V → V → ℕ) (f g : V → ℕ) {q e δ h : ℝ}
    (hn : 0 < Fintype.card V) (_he : 0 ≤ e) (heq : e < q)
    (hδ : 0 ≤ δ) (hδsmall : δ < 1 / 4)
    (hmargin : 2 * e / (q - e) ≤ δ)
    (hcapacity : q + e ≤ h * Fintype.card V / 2)
    (htotal : ∑ x, f x = ∑ y, g y)
    (hf : ∀ x, q - e ≤ (f x : ℝ) ∧ (f x : ℝ) ≤ q + e)
    (hg : ∀ y, q - e ≤ (g y : ℝ) ∧ (g y : ℝ) ≤ q + e)
    (hlarge : ∀ (S T : Finset V),
      1 - 2 * δ < (S.card : ℝ) / Fintype.card V + (T.card : ℝ) / Fintype.card V →
      h * Fintype.card V * Fintype.card V *
          min ((S.card : ℝ) / Fintype.card V) ((T.card : ℝ) / Fintype.card V) ≤
        ((∑ x, ∑ y, if x ∈ S ∧ y ∈ T then L x y else 0 : ℕ) : ℝ)) :
    ∀ (S T : Finset V), ∑ x ∈ S, f x ≤ (∑ y ∈ T, g y) +
      ∑ x, ∑ y, if x ∈ S ∧ y ∉ T then L x y else 0 := by
  classical
  let M : ℝ := ∑ x, (f x : ℝ)
  have hn' : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr hn
  have hM : 0 ≤ M := Finset.sum_nonneg (fun x _ => Nat.cast_nonneg (f x))
  have htotal' : ∑ y, (g y : ℝ) = M := by
    dsimp [M]
    exact_mod_cast htotal.symm
  have hMlow : Fintype.card V * (q - e) ≤ M := by
    calc
      _ = ∑ _ : V, (q - e) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun x _ => (hf x).1)
  have hMhigh : M ≤ Fintype.card V * (q + e) := by
    calc
      _ ≤ ∑ _ : V, (q + e) := Finset.sum_le_sum (fun x _ => (hf x).2)
      _ = _ := by simp; ring
  have hMC : M ≤ h * Fintype.card V * Fintype.card V / 2 := by
    have hs := mul_le_mul_of_nonneg_left hcapacity hn'.le
    nlinarith
  have hrelative : Fintype.card V * (q + e) ≤ (1 + δ) * M := by
    have hb := (div_le_iff₀ (sub_pos.mpr heq)).mp hmargin
    have hb' := mul_le_mul_of_nonneg_left hb hn'.le
    have hmδ := mul_le_mul_of_nonneg_left hMlow hδ
    nlinarith
  have hupper (z : ℝ) (hz : z ≤ q + e) :
      z ≤ (1 + δ) * M / Fintype.card V := by
    apply (le_div_iff₀ hn').mpr
    have hz' := mul_le_mul_of_nonneg_left hz hn'.le
    nlinarith
  exact nearUniformMultiplicity_cut L f g hn hδ hδsmall hM hMC
    rfl htotal' (fun x => hupper _ (hf x).2) (fun y => hupper _ (hg y).2) hlarge

end Oberwolfach
