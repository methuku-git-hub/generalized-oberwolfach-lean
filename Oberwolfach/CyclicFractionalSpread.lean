module

public import Oberwolfach.CyclicFractionalBounded
public import Oberwolfach.CyclicPairLoad

@[expose] public section

/-! Positive bounded fractional cycle weights and both pair-load estimates
for the same decomposition of the given cyclic graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclicInterfaceGraph_fractional_cycles_with_pair_bounds {k : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    (L : Fin (k + 2) → X → X → Prop) (R : Fin (k + 2) → X → X → Prop)
    (δ α : ℝ) (hn : 0 < Fintype.card X) (hα : 0 < α)
    (hthreshold : ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card X ≤
      (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hdY : ∀ i y, δ ≤ (Finset.univ.filter (fun x => L i x y)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card) :
    ∃ w : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) → ℝ,
      (∀ H, 0 ≤ w H) ∧
      (∀ H, 0 < w H → H ≤ cyclicInterfaceGraph L R ∧
        IsEmbeddedCycle H ((k + 2) * 2) ∧
          ∃ p : Fin (k + 2) → X × X × X, H = alternatingTupleGraph p) ∧
      (∀ u v, (∑ H, if H.Adj u v then w H else 0) =
        if (cyclicInterfaceGraph L R).Adj u v then 1 else 0) ∧
      (∀ H, H ≤ cyclicInterfaceGraph L R →
        (∃ p : Fin (k + 2) → X × X × X, H = alternatingTupleGraph p) →
        ((k + 2 : ℝ) * cyclicSectorLower k α) / (Fintype.card X : ℝ) ^ (2 * k + 2) ≤ w H ∧
        w H ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
          (Fintype.card X : ℝ) ^ (2 * k + 2)) ∧
      (∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        (∑ H, if H.Adj a b ∧ H.Adj a c then w H else 0) ≤
          ((k + 2 : ℝ) * cyclicSectorUpper k α) / Fintype.card X) ∧
      (∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        (∑ H, if H.Adj a b ∧ H.Adj c d then w H else 0) ≤
          ((k + 2 : ℝ) * cyclicSectorUpper k α) / (Fintype.card X : ℝ) ^ 2) := by
  obtain ⟨w, hw, hs, he, hpoint⟩ := cyclicInterfaceGraph_fractional_cycles_bounded
    L R δ α hn hα rfl hthreshold hdL hdY hY hX
  have hB : 0 ≤ (k + 2 : ℝ) * cyclicSectorUpper k α :=
    (mul_pos (by positivity) (cyclicSectorConstants_pos k α hα).2).le
  have hn' : (0 : ℝ) < Fintype.card X := by exact_mod_cast hn
  have hsupport (H) (hH : 0 < w H) : H ∈ Set.range (cyclicSelectionGraph (k := k) (X := X)) := by
    obtain ⟨p, hp⟩ := (hs H hH).2.2
    exact ⟨cyclicSelectionOfTuple p, (cyclicSelectionGraph_ofTuple p).trans hp.symm⟩
  have hbound (f : Fin (k + 2) ⊕ Fin (k + 2) → X) :
      w (cyclicSelectionGraph f) ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
        (Fintype.card X : ℝ) ^ (2 * k + 2) := by
    by_cases hz : w (cyclicSelectionGraph f) = 0
    · rw [hz]
      exact div_nonneg hB (pow_pos hn' _).le
    · have hp := lt_of_le_of_ne (hw _) (Ne.symm hz)
      exact (hpoint _ (hs _ hp).1 (hs _ hp).2.2).2
  refine ⟨w, hw, hs, he, hpoint, ?_, ?_⟩
  · intro a b c hab hac hbc
    exact cyclic_graph_adjacent_pair_load w hw hsupport _ hB hn hbound a b c hab hac hbc
  · intro a b c d hab hac had hbc hbd hcd
    exact cyclic_graph_disjoint_pair_load w hw hsupport _ hB hn hbound a b c d hab hac had hbc hbd hcd

end Oberwolfach
