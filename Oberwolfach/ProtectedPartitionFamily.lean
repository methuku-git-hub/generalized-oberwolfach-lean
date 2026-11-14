module

public import Oberwolfach.ProtectedRegularSample
public import Oberwolfach.ProtectedSets

@[expose] public section

/-! The protected-set and colour-specific-error formulation used by the
manuscript. Both families of lower bounds precede the choice of the order
threshold; the protected graphs are selected only after the colouring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protectedRegularPartition_family_highProbability
    {k : ℕ} (hk : 0 < k) {α : ℝ} (hα : 0 < α)
    (r ξ : Fin k → ℝ) (hr : ∀ a, 0 < r a) (hξ : ∀ a, 0 < ξ a) (B : ℕ) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G : SimpleGraph (Fin n)) (D : ℕ)
      (m : Fin k → ℕ) (ρ : Fin k → ℝ)
      (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1),
      G.IsRegularOfDegree D → Even D → (1 / 2 + α) * n ≤ (D : ℝ) →
      (∑ a, m a = D / 2) → (∀ a, ρ a / 2 * D = (m a : ℝ)) →
      (∀ a, r a ≤ ρ a) → ∀ I : Fin k → Finset (Fin n),
      ((∑ a, (I a).card : ℕ) : ℝ) ≤ α / 100000 * n →
      1 - 1 / (n : ℝ) ^ 10 ≤
        (FiniteLaw.pi (fun _ : Sym2 (Fin n) => FiniteLaw.categorical ρ hρ htotal)).probability
          (fun c => ∀ A : Fin k → SimpleGraph (Fin n),
            (∀ a, A a ≤ edgeColourGraph G c a) →
            (∑ a, (A a).edgeFinset.card) ≤ B →
            ∃ H : Fin k → SimpleGraph (Fin n),
              EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
              (∀ a, A a ≤ H a) ∧
              (∀ a b x, x ∈ I b → ∀ y, y ∈ I b →
                ((H a).Adj x y ↔ (edgeColourGraph G c a).Adj x y)) ∧
              (∀ a x, ((Finset.univ.filter (fun y =>
                Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card : ℝ) ≤ ξ a * n)) := by
  obtain ⟨r₀, hr₀, hrle⟩ := positive_common_lower_bound hk r hr
  obtain ⟨ξ₀, hξ₀, hξle⟩ := positive_common_lower_bound hk ξ hξ
  obtain ⟨N₀, hN⟩ := protectedRegularPartition_highProbability k hα hr₀ hξ₀ B
  refine ⟨N₀, fun n hn G D m ρ hρ htotal hreg heven hmin hsum hm hrlow I hI => ?_⟩
  let Z := protectedInducedUnion G I
  have hZ (x : Fin n) : (Z.degree x : ℝ) ≤ α / 100000 * n := by
    have hh : (Z.degree x : ℝ) ≤ (∑ a, (I a).card : ℕ) := by
      exact_mod_cast protectedInducedUnion_degree G I x
    exact hh.trans hI
  have hp := hN n hn G Z D m ρ hρ htotal hreg heven hmin hsum hm
    (fun a => (hrle a).trans (hrlow a)) hZ
  apply hp.trans
  apply finiteLaw_probability_mono
  intro c hc A hA hsize
  let U := Finset.univ.biUnion (fun a => (A a).edgeFinset)
  let F := SimpleGraph.fromEdgeSet (U : Set (Sym2 (Fin n)))
  have hF (x : Fin n) : F.degree x ≤ B := by
    have hu : U.card ≤ ∑ a, (A a).edgeFinset.card := Finset.card_biUnion_le
    have hh := (graphFromFiniteEdges_degree U x).trans (hu.trans hsize)
    simpa only [← SimpleGraph.ncard_neighborSet] using hh
  obtain ⟨H, hH, hregH, hfixed, hdiff⟩ := hc F (fun x => by simpa only [← SimpleGraph.ncard_neighborSet] using hF x)
  have hret (a : Fin k) : A a ≤ H a := by
    intro x y hxy
    have he : s(x,y) ∈ U := by
      apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_univ _, by simpa using hxy⟩
    have hf : F.Adj x y := ⟨he, (A a).ne_of_adj hxy⟩
    exact (hfixed a x y (Or.inr hf)).mpr (hA a hxy)
  have hind (a b : Fin k) (x : Fin n) (hx : x ∈ I b) (y : Fin n) (hy : y ∈ I b) :
      (H a).Adj x y ↔ (edgeColourGraph G c a).Adj x y := by
    by_cases hg : G.Adj x y
    · have hz : Z.Adj x y := ⟨hg, b, hx, hy⟩
      exact hfixed a x y (Or.inl hz)
    · have hh : ¬ (H a).Adj x y := fun h => hg ((hH x y).1.mpr ⟨a, h⟩)
      have hc' : ¬ (edgeColourGraph G c a).Adj x y := fun h => hg h.1
      simp [hh, hc']
  exact ⟨H, hH, hregH, hret, hind, fun a x =>
    (hdiff a x).trans (mul_le_mul_of_nonneg_right (hξle a) (Nat.cast_nonneg n))⟩

end Oberwolfach
