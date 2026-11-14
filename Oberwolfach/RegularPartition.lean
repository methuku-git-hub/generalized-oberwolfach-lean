module

public import Oberwolfach.Definitions
public import Oberwolfach.BipartiteEdgeColouring

@[expose] public section

/-!
Projection of directed multiplicities to physical simple-graph partitions,
and the last equal-degree grouping step in `lem:family:partition`.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Splitting the directed incidence graph into equal-degree parts gives an
edge partition of the original simple graph, with twice the directed degree.
The pointwise hypothesis records both orientations of each physical edge
exactly once, and rules out loops and opposite directed copies. -/
theorem regularPartition_of_orientedMultiplicities
    {n k : ℕ} (G : SimpleGraph (Fin n))
    (Q : Fin k → Fin n → Fin n → ℕ) (m : Fin k → ℕ)
    (hphysical : ∀ x y, (∑ a, Q a x y) + (∑ a, Q a y x) =
      if G.Adj x y then 1 else 0)
    (hout : ∀ a x, ∑ y, Q a x y = m a)
    (hin : ∀ a y, ∑ x, Q a x y = m a) :
    ∃ H : Fin k → SimpleGraph (Fin n),
      EdgePartition G H ∧ (∀ a, (H a).IsRegularOfDegree (2 * m a)) ∧
      ∀ a x y, (H a).Adj x y ↔ 0 < Q a x y + Q a y x := by
  let W (a : Fin k) (x y : Fin n) := Q a x y + Q a y x
  have hWsum (x y : Fin n) : ∑ a, W a x y = if G.Adj x y then 1 else 0 := by
    simp only [W, Finset.sum_add_distrib]
    exact hphysical x y
  have hWle (a : Fin k) (x y : Fin n) : W a x y ≤ if G.Adj x y then 1 else 0 := by
    rw [← hWsum]
    exact Finset.single_le_sum (fun b _ => Nat.zero_le (W b x y)) (Finset.mem_univ a)
  let H : Fin k → SimpleGraph (Fin n) := fun a =>
    { Adj := fun x y => 0 < W a x y
      symm := by
        constructor
        intro x y h
        simpa only [W, Nat.add_comm] using h
      loopless := by
        constructor
        intro x h
        have hz : W a x x ≤ 0 := by simpa using hWle a x x
        omega }
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x y
    constructor
    · change G.Adj x y ↔ ∃ a, 0 < W a x y
      have hp : (0 < ∑ a, W a x y) ↔ ∃ a, 0 < W a x y := by
        simp only [Finset.sum_pos_iff, Finset.mem_univ, true_and]
      rw [← hp, hWsum]
      split_ifs <;> simp_all
    · intro a b ha hb
      change 0 < W a x y at ha
      change 0 < W b x y at hb
      by_contra hab
      have hbmem : b ∈ Finset.univ.erase a :=
        Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
      have hb' : W b x y ≤ ∑ c ∈ Finset.univ.erase a, W c x y :=
        Finset.single_le_sum (fun c _ => Nat.zero_le (W c x y)) hbmem
      have hs := Finset.sum_erase_add Finset.univ (fun c => W c x y)
        (Finset.mem_univ a)
      have ht : ∑ c, W c x y ≤ 1 := by
        rw [hWsum]
        split_ifs <;> omega
      omega
  · intro a x
    have hind (y : Fin n) : (if (H a).Adj x y then 1 else 0 : ℕ) = W a x y := by
      change (if 0 < W a x y then 1 else 0 : ℕ) = W a x y
      have hb : W a x y ≤ 1 := (hWle a x y).trans (by split_ifs <;> omega)
      split_ifs <;> omega
    rw [SimpleGraph.degree]
    calc
      _ = (Finset.univ.filter (fun y => (H a).Adj x y)).card := by
        congr 1
        ext y
        simp
      _ = ∑ y, W a x y := by rw [Finset.card_filter]; simp only [hind]
      _ = 2 * m a := by
        simp only [W, Finset.sum_add_distrib, hout, hin]
        omega

  · intro a x y
    rfl

/-- Equal-degree grouping of an already constructed balanced orientation. -/
theorem regularPartition_of_balancedOrientation
    {n k q : ℕ} (G : SimpleGraph (Fin n))
    (M : Fin n → Fin n → ℕ)
    (hphysical : ∀ x y, M x y + M y x = if G.Adj x y then 1 else 0)
    (hout : ∀ x, ∑ y, M x y = k * q)
    (hin : ∀ y, ∑ x, M x y = k * q) :
    ∃ H : Fin k → SimpleGraph (Fin n),
      EdgePartition G H ∧ ∀ a, (H a).IsRegularOfDegree (2 * q) := by
  obtain ⟨Q, hQsum, hQout, hQin⟩ :=
    regularBipartite_groupedDecomposition k q M hout hin
  obtain ⟨H, hH, hdegrees, _⟩ := regularPartition_of_orientedMultiplicities
    G Q (fun _ => q) (by simpa only [hQsum] using hphysical) hQout hQin
  exact ⟨H, hH, hdegrees⟩

end Oberwolfach
