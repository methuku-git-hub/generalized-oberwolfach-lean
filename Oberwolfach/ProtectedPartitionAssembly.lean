module

public import Oberwolfach.ProtectedPartition
public import Oberwolfach.ColourReorientation

@[expose] public section

/-! Deterministic assembly from the original colour sample and a balanced
orientation. All cuts are checked after excluding the protected graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protectedPartition_from_balancing
    {n k q : ℕ} (G F : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Fin k)
    (M₀ N : Fin n → Fin n → ℕ) (m : Fin k → ℕ) (δ h f : Fin k → ℝ)
    {t b e : ℝ} (hn : 0 < n) (he : 0 ≤ e) (heq : e < q)
    (hq : ∀ a, q ≤ m a) (hte : t + b ≤ e)
    (hphys₀ : ∀ x y, M₀ x y + M₀ y x = if G.Adj x y then 1 else 0)
    (hphys : ∀ x y, N x y + N y x = if G.Adj x y then 1 else 0)
    (hout : ∀ x, ∑ y, N x y = ∑ a, m a)
    (hin : ∀ y, ∑ x, N x y = ∑ a, m a)
    (hnearout : ∀ a x, |((∑ y, colourRestriction c M₀ a x y : ℕ) : ℝ) - m a| ≤ t)
    (hnearin : ∀ a y, |((∑ x, colourRestriction c M₀ a x y : ℕ) : ℝ) - m a| ≤ t)
    (hchange : ∀ x, ((Finset.univ.filter (fun y => M₀ x y ≠ N x y ∨ M₀ y x ≠ N y x)).card : ℝ) ≤ b)
    (hforbid : ∀ a x, (sampledColourDegree F c a x : ℝ) ≤ f a)
    (hδ : ∀ a, 0 ≤ δ a ∧ δ a < 1 / 4)
    (hmargin : ∀ a, 2 * e / ((q : ℝ) - e) ≤ δ a)
    (hcapacity : ∀ a, (q : ℝ) + e ≤ h a * n / 2)
    (hloss : ∀ a, f a + b ≤ h a * n)
    (hrawcut : ∀ a (S T : Finset (Fin n)),
      (1 - 2 * δ a) * n < (S.card : ℝ) + T.card →
      2 * h a * n * min (S.card : ℝ) T.card ≤
        (matrixCut (colourRestriction c M₀ a) S T : ℝ)) :
    ∃ H : Fin k → SimpleGraph (Fin n),
      EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
      (∀ a x y, F.Adj x y → ((H a).Adj x y ↔ (edgeColourGraph G c a).Adj x y)) ∧
      (∀ a x, ((Finset.univ.filter (fun y =>
        Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card : ℝ) ≤ 4 * q + 2 * e) := by
  let M := colourRestriction c N
  let L (a : Fin k) := excludeGraph F (M a)
  have hN (x y : Fin n) : N x y ≤ 1 := by
    have hh := hphys x y
    split_ifs at hh <;> omega
  have hM₀ (x y : Fin n) : M₀ x y ≤ 1 := by
    have hh := hphys₀ x y
    split_ifs at hh <;> omega
  have hL (a : Fin k) (x y : Fin n) : L a x y ≤ M a x y := by
    dsimp [L, excludeGraph]
    split_ifs <;> omega
  have hphysical (x y : Fin n) : (∑ a, M a x y) + (∑ a, M a y x) =
      if G.Adj x y then 1 else 0 := by
    simpa only [M, colourRestriction_sum] using hphys x y
  have hmout (x : Fin n) : ∑ a, ∑ y, M a x y = ∑ a, m a := by
    rw [Finset.sum_comm]
    simpa only [M, colourRestriction_sum] using hout x
  have hmin (y : Fin n) : ∑ a, ∑ x, M a x y = ∑ a, m a := by
    rw [Finset.sum_comm]
    simpa only [M, colourRestriction_sum] using hin y
  have hnear (a : Fin k) (x : Fin n) :
      (m a : ℝ) - e ≤ ((∑ y, M a x y : ℕ) : ℝ) ∧
      ((∑ y, M a x y : ℕ) : ℝ) ≤ m a + e := by
    have h₀ := abs_le.mp (hnearout a x)
    have hs := abs_le.mp ((colourRestriction_degree_stability c M₀ N hM₀ hN a x).trans (hchange x))
    dsimp [M]
    constructor <;> linarith [h₀.1, h₀.2, hs.1, hs.2]
  have hneari (a : Fin k) (x : Fin n) :
      (m a : ℝ) - e ≤ ((∑ y, M a y x : ℕ) : ℝ) ∧
      ((∑ y, M a y x : ℕ) : ℝ) ≤ m a + e := by
    have h₀ := abs_le.mp (hnearin a x)
    have hs := abs_le.mp ((colourRestriction_indegree_stability c M₀ N hM₀ hN a x).trans (hchange x))
    dsimp [M]
    constructor <;> linarith [h₀.1, h₀.2, hs.1, hs.2]
  have hlarge (a : Fin k) (S T : Finset (Fin n))
      (hST : 1 - 2 * δ a < (S.card : ℝ) / n + (T.card : ℝ) / n) :
      h a * n * n * min ((S.card : ℝ) / n) ((T.card : ℝ) / n) ≤
        ((∑ x, ∑ y, if x ∈ S ∧ y ∈ T then L a x y else 0 : ℕ) : ℝ) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hST' : (1 - 2 * δ a) * n < (S.card : ℝ) + T.card := by
      rw [← add_div] at hST
      exact (lt_div_iff₀ hnpos).mp hST
    have hcut := hrawcut a S T hST'
    have hbound := colourReorientation_cut_loss c M₀ N F hM₀ hchange hforbid a S T
    have hl := mul_le_mul_of_nonneg_right (hloss a)
      (show (0 : ℝ) ≤ min (S.card : ℝ) T.card by positivity)
    have heq : h a * n * n * min ((S.card : ℝ) / n) ((T.card : ℝ) / n) =
        h a * n * min (S.card : ℝ) T.card := by
      rw [min_div_div_right hnpos.le]
      field_simp
    rw [heq]
    have hsum : (∑ x, ∑ y, if x ∈ S ∧ y ∈ T then L a x y else 0) = matrixCut (L a) S T := by
      simp only [matrixCut, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_mem, Finset.univ_inter]
    rw [hsum]
    change _ ≤ (matrixCut (excludeGraph F (colourRestriction c N a)) S T : ℝ)
    nlinarith
  have hzero (a : Fin k) (x y : Fin n) (hf : F.Adj x y) : L a x y = 0 ∧ L a y x = 0 := by
    simp [L, excludeGraph, hf, hf.symm]
  obtain ⟨H, hH, hreg, hfixed, hdiff⟩ := protectedRegularPartition_of_largeCuts G m M L F.Adj δ h
    hn he heq hq hL hphysical hmout hmin hnear hneari hδ hmargin hcapacity hlarge hzero
  refine ⟨H, hH, hreg, ?_, ?_⟩
  · intro a x y hf
    exact (hfixed a x y hf).trans (colourRestriction_underlying G c N hphys a x y)
  · intro a x
    simpa only [M, colourRestriction_underlying G c N hphys] using hdiff a x

end Oberwolfach
