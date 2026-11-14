module

public import Oberwolfach.ProtectedPartitionAssembly
public import Oberwolfach.ProtectedSampling
public import Oberwolfach.RawColourCutBounds
public import Oberwolfach.PartitionMargins

@[expose] public section

/-! Protected regular partition from the actual independent colour law.
The fixed protected graph is chosen before sampling. All graphs with the
specified bounded degree may be protected afterwards on the same event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem piProbability_decEq {E : Type*} [Fintype E]
    {S : E → Type*} [∀ e, Fintype (S e)]
    (d₁ d₂ : DecidableEq E) (μ : ∀ e, FiniteLaw (S e))
    (A : (∀ e, S e) → Prop) :
    (letI : DecidableEq E := d₁; (FiniteLaw.pi μ).probability A) =
      (letI : DecidableEq E := d₂; (FiniteLaw.pi μ).probability A) := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  cases h
  rfl


theorem protectedRegularPartition_highProbability (k : ℕ) {α r ξ : ℝ}
    (hα : 0 < α) (hr : 0 < r) (hξ : 0 < ξ) (B : ℕ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G Z : SimpleGraph (Fin n)) (D : ℕ)
      (m : Fin k → ℕ) (ρ : Fin k → ℝ)
      (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1),
      G.IsRegularOfDegree D → Even D → (1 / 2 + α) * n ≤ (D : ℝ) →
      (∑ a, m a = D / 2) → (∀ a, ρ a / 2 * D = (m a : ℝ)) →
      (∀ a, r ≤ ρ a) → (∀ x, (Z.degree x : ℝ) ≤ α / 100000 * n) →
      1 - 1 / (n : ℝ) ^ 10 ≤
        (FiniteLaw.pi (fun _ : Sym2 (Fin n) => FiniteLaw.categorical ρ hρ htotal)).probability
          (fun c => ∀ A : SimpleGraph (Fin n), (∀ x, A.degree x ≤ B) →
            ∃ H : Fin k → SimpleGraph (Fin n),
              EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
              (∀ a x y, (Z ⊔ A).Adj x y →
                ((H a).Adj x y ↔ (edgeColourGraph G c a).Adj x y)) ∧
              (∀ a x, ((Finset.univ.filter (fun y =>
                Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card : ℝ) ≤ ξ * n)) := by
  let qstar := min (ξ / 16) (min (α * r / 2048) (r / 64))
  have hqstar : 0 < qstar := by dsimp [qstar]; positivity
  have hqx : qstar ≤ ξ / 16 := min_le_left _ _
  have hqh : qstar ≤ α * r / 2048 := (min_le_right _ _).trans (min_le_left _ _)
  have hqr : qstar ≤ r / 64 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₁, h₁⟩ := eventually_partition_margins hα hr hξ hqstar hqx hqh hqr B
  obtain ⟨N₂, h₂⟩ := protectedSample_highProbability k 10 hα
    (q := α * r ^ 2 / 1024) (by positivity)
  refine ⟨max N₁ N₂, fun n hn G Z D m ρ hρ htotal hreg heven hmin hsum hm hrlow hZ => ?_⟩
  obtain ⟨hn2, heq, hqsmall, hmargin, hcapacity, hdiff, ht, hloss, hFmargin⟩ :=
    h₁ n (le_trans (le_max_left _ _) hn)
  have hnpos : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let v : Fin n := ⟨0, hnpos⟩
  have hDmax : (D : ℝ) < n := by
    have hh := G.degree_lt_card_verts v
    rw [hreg v, Fintype.card_fin] at hh
    exact_mod_cast hh
  have hαmax : α ≤ 1 / 2 := by nlinarith
  have hdegree (x : Fin n) : (1 / 2 + α) * Fintype.card (Fin n) ≤ (G.degree x : ℝ) := by
    simpa only [Fintype.card_fin, hreg x] using hmin
  have hevendeg (x : Fin n) : Even (G.degree x) := by rw [hreg x]; exact heven
  have hsamp := h₂ (Fin n) (by simpa using le_trans (le_max_right _ _) hn) G Z ρ hρ htotal hevendeg hdegree
  simp only [Fintype.card_fin] at hsamp
  have hsamp' : 1 - 1 / (n : ℝ) ^ 10 ≤
      (FiniteLaw.pi (fun _ : Sym2 (Fin n) => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
        (ProtectedSampleGood G Z ρ α (α * r ^ 2 / 1024)) := by
    convert hsamp using 1
    exact piProbability_decEq (E := Sym2 (Fin n)) (S := fun _ => Fin k × Bool) _ _
      (fun _ => FiniteLaw.categoricalDirection ρ hρ htotal) _
  let E := fun c : Sym2 (Fin n) → Fin k => ∀ A : SimpleGraph (Fin n),
    (∀ x, A.degree x ≤ B) → ∃ H : Fin k → SimpleGraph (Fin n),
      EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
      (∀ a x y, (Z ⊔ A).Adj x y → ((H a).Adj x y ↔ (edgeColourGraph G c a).Adj x y)) ∧
      (∀ a x, ((Finset.univ.filter (fun y =>
        Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card : ℝ) ≤ ξ * n)
  change _ ≤ (FiniteLaw.pi (fun _ : Sym2 (Fin n) => FiniteLaw.categorical ρ hρ htotal)).probability E
  rw [← categoricalDirection_colour_probability ρ hρ htotal E]
  apply hsamp'.trans
  refine finiteLaw_probability_mono (FiniteLaw.pi (fun _ : Sym2 (Fin n) => FiniteLaw.categoricalDirection ρ hρ htotal))
    (ProtectedSampleGood G Z ρ α (α * r ^ 2 / 1024)) (fun σ => E (fun e => (σ e).1)) ?_
  intro σ hσ A hA
  let c := fun e => (σ e).1
  let M₀ := sampledOrientation G (fun e => (σ e).2)
  let F := Z ⊔ A
  have hF (x : Fin n) : (F.degree x : ℝ) ≤ α * Fintype.card (Fin n) / 100 := by
    have hh := graph_sup_degree_le Z A x
    have hhr : (F.degree x : ℝ) ≤ (Z.degree x : ℝ) + A.degree x := by exact_mod_cast hh
    have hAr : (A.degree x : ℝ) ≤ B := by exact_mod_cast hA x
    simp only [Fintype.card_fin]
    linarith [hZ x]
  obtain ⟨N, hphys, hbal, _havoid, hchange⟩ := hσ.balance F (fun x => by simpa only [← SimpleGraph.ncard_neighborSet] using hF x)
  have hchange' (x : Fin n) :
      ((Finset.univ.filter (fun y => M₀ x y ≠ N x y ∨ M₀ y x ≠ N y x)).card : ℝ) ≤
        4 * (n : ℝ) ^ (4 / 5 : ℝ) := by
    simpa only [M₀, ne_comm, Fintype.card_fin] using hchange x
  let t := (n : ℝ) ^ (3 / 5 : ℝ)
  let b := 4 * (n : ℝ) ^ (4 / 5 : ℝ)
  let e := 5 * (n : ℝ) ^ (4 / 5 : ℝ)
  let q := Nat.floor (qstar * n)
  let δ (a : Fin k) := min (α / 32) (ρ a / 512)
  let h (a : Fin k) := α * ρ a / 128
  let f (a : Fin k) := ρ a * (α / 100000 * n) + t + B
  have hmrow (a : Fin k) (x : Fin n) :
      |((∑ y, colourRestriction c M₀ a x y : ℕ) : ℝ) - m a| ≤ t := by
    have hh := (hσ.degrees a x).1.le
    simpa only [Fintype.card_fin, hreg x, hm a, sampledColourOrientation_eq_restriction, c, M₀, t] using hh
  have hmcol (a : Fin k) (x : Fin n) :
      |((∑ y, colourRestriction c M₀ a y x : ℕ) : ℝ) - m a| ≤ t := by
    have hh := (hσ.degrees a x).2.1.le
    simpa only [Fintype.card_fin, hreg x, hm a, sampledColourOrientation_eq_restriction, c, M₀, t] using hh
  have hforbid (a : Fin k) (x : Fin n) : (sampledColourDegree F c a x : ℝ) ≤ f a := by
    have hh := (abs_lt.mp (hσ.degrees a x).2.2).2
    have hsup := sampledColourDegree_sup_le Z A c a x
    have hsupr : (sampledColourDegree F c a x : ℝ) ≤
        (sampledColourDegree Z c a x : ℝ) + A.degree x := by exact_mod_cast hsup
    have hAr : (A.degree x : ℝ) ≤ B := by exact_mod_cast hA x
    have hz := mul_le_mul_of_nonneg_left (hZ x) (hρ a)
    simp only [Fintype.card_fin] at hh
    dsimp [f, t, c] at *
    linarith
  have hρn (a : Fin k) : r * n / 4 ≤ (m a : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmin (hρ a)
    have hl := mul_le_mul_of_nonneg_right (hrlow a) hnr.le
    rw [← hm a]
    nlinarith [mul_nonneg hα.le (mul_nonneg (hρ a) hnr.le)]
  have hq (a : Fin k) : q ≤ m a := by
    have hh : (q : ℝ) ≤ m a := hqsmall.trans (hρn a)
    exact_mod_cast hh
  have hδ (a : Fin k) : 0 ≤ δ a ∧ δ a < 1 / 4 := by
    constructor
    · exact le_min (by positivity) (div_nonneg (hρ a) (by norm_num))
    · have hh : δ a ≤ α / 32 := min_le_left _ _
      linarith
  have hmargin' (a : Fin k) : 2 * e / ((q : ℝ) - e) ≤ δ a := by
    apply hmargin.trans
    exact min_le_min le_rfl (div_le_div_of_nonneg_right (hrlow a) (by norm_num))
  have hcapacity' (a : Fin k) : (q : ℝ) + e ≤ h a * n / 2 := by
    have hh := mul_le_mul_of_nonneg_left (hrlow a) hα.le
    have hh' := mul_le_mul_of_nonneg_right hh hnr.le
    dsimp [h]
    linarith
  have hloss' (a : Fin k) : f a + b ≤ h a * n := by
    have hh := mul_le_mul_of_nonneg_left (hrlow a) hα.le
    have hh' := mul_le_mul_of_nonneg_right hh hnr.le
    dsimp [f, b, h, t]
    nlinarith [mul_nonneg hα.le (mul_nonneg (hρ a) hnr.le)]
  have hrawcut (a : Fin k) (S T : Finset (Fin n))
      (hST : (1 - 2 * δ a) * n < (S.card : ℝ) + T.card) :
      2 * h a * n * min (S.card : ℝ) T.card ≤
        (matrixCut (colourRestriction c M₀ a) S T : ℝ) := by
    have hm0 (x y : Fin n) : colourRestriction c M₀ a x y ≤ 1 := by
      apply (colourRestriction_le c M₀ a x y).trans
      dsimp [M₀, sampledOrientation]
      split_ifs <;> omega
    have hlow : ρ a * n / 4 ≤ (m a : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hmin (hρ a)
      rw [← hm a]
      nlinarith [mul_nonneg hα.le (mul_nonneg (hρ a) hnr.le)]
    have hrw (x : Fin n) : ρ a * Fintype.card (Fin n) / 4 - t ≤
        ((∑ y, colourRestriction c M₀ a x y : ℕ) : ℝ) := by
      simp only [Fintype.card_fin]
      linarith [(abs_le.mp (hmrow a x)).1]
    have hcl (x : Fin n) : ρ a * Fintype.card (Fin n) / 4 - t ≤
        ((∑ y, colourRestriction c M₀ a y x : ℕ) : ℝ) := by
      simp only [Fintype.card_fin]
      linarith [(abs_le.mp (hmcol a x)).1]
    have ht' : t ≤ ρ a * Fintype.card (Fin n) / 32 := by
      have hh := mul_le_mul_of_nonneg_right (hrlow a) hnr.le
      simp only [Fintype.card_fin]
      linarith
    have hcut (S T : Finset (Fin n)) :
        |(matrixCut (colourRestriction c M₀ a) S T : ℝ) - ρ a / 2 * graphCut G S T| <
          (α * r ^ 2 / 1024) * (Fintype.card (Fin n) : ℝ) ^ 2 := by
      simpa only [matrixCut, sampledColourOrientation_eq_restriction, c, M₀] using hσ.cuts a S T
    have hqcut : α * r ^ 2 / 1024 ≤ α * (ρ a) ^ 2 / 1024 := by
      have hh : r ^ 2 ≤ (ρ a) ^ 2 := by nlinarith [hrlow a, hρ a]
      nlinarith [mul_le_mul_of_nonneg_left hh hα.le]
    have hh := matrixCut_large_of_degree_and_quadratic G (colourRestriction c M₀ a)
      hα.le hαmax (hρ a) (show δ a ≤ α / 32 from min_le_left _ _)
      (show δ a ≤ ρ a / 512 from min_le_right _ _) ht' hqcut hm0 hdegree hrw hcl hcut S T
      (by simpa only [Fintype.card_fin] using hST)
    simp only [Fintype.card_fin] at hh
    dsimp [h]
    nlinarith
  have hte : t + b ≤ e := by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1 (show (3 / 5 : ℝ) ≤ 4 / 5 by norm_num)
    dsimp [t, b, e]
    linarith
  obtain ⟨H, hH, hregH, hfixed, hsize⟩ := protectedPartition_from_balancing G F c M₀ N m δ h f
    hnpos (by positivity) heq hq hte
    (sampledOrientation_physical G (fun e => (σ e).2)) hphys
    (fun x => by rw [(hbal x).1, hreg x, hsum])
    (fun x => by rw [(hbal x).2, hreg x, hsum])
    hmrow hmcol hchange' hforbid hδ hmargin' hcapacity' hloss' hrawcut
  exact ⟨H, hH, hregH, hfixed, fun a x => (hsize a x).trans hdiff⟩

end Oberwolfach
