module

public import Oberwolfach.CyclicSelections
public import Oberwolfach.TransversalWeightBounds

@[expose] public section

/-! Pair-load bounds from the exact number of prescribed class vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclic_graph_event_load_bound {k : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X]
    (w : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) → ℝ)
    (hw : ∀ H, 0 ≤ w H)
    (hs : ∀ H, 0 < w H → H ∈ Set.range (cyclicSelectionGraph (k := k) (X := X)))
    (B : ℝ) (hB : 0 ≤ B) (hn : 0 < Fintype.card X)
    (hb : ∀ f, w (cyclicSelectionGraph f) ≤ B / (Fintype.card X : ℝ) ^ (2 * k + 2))
    (S : Finset ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)))
    (hS : 2 ≤ S.card) (hSd : S.card ≤ 2 * (k + 2))
    (E : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) → Prop)
    (hE : ∀ f, E (cyclicSelectionGraph f) →
      ∀ v ∈ S, f (taggedClass v) = taggedValue v) :
    (∑ H, if E H then w H else 0) ≤ B / (Fintype.card X : ℝ) ^ (S.card - 2) := by
  have hn' : (0 : ℝ) < Fintype.card X := by exact_mod_cast hn
  have hh := transversal_graph_weight_bound taggedClass taggedValue
    taggedEncoding_injective cyclicSelectionGraph cyclicSelectionGraph_injective
    w hw hs (B / (Fintype.card X : ℝ) ^ (2 * k + 2))
    (div_nonneg hB (pow_pos hn' _).le) hb S E hE
  have hdim : Fintype.card (Fin (k + 2) ⊕ Fin (k + 2)) = 2 * (k + 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  rw [hdim] at hh
  have hexp : 2 * k + 2 = 2 * (k + 2) - 2 := by omega
  rw [hexp, normalized_transversal_power _ _ _ _ hn'.ne' hS hSd] at hh
  exact hh

theorem cyclic_graph_adjacent_pair_load {k : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X]
    (w : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) → ℝ)
    (hw : ∀ H, 0 ≤ w H)
    (hs : ∀ H, 0 < w H → H ∈ Set.range (cyclicSelectionGraph (k := k) (X := X)))
    (B : ℝ) (hB : 0 ≤ B) (hn : 0 < Fintype.card X)
    (hb : ∀ f, w (cyclicSelectionGraph f) ≤ B / (Fintype.card X : ℝ) ^ (2 * k + 2))
    (a b c : (Fin (k + 2) × X) ⊕ (Fin (k + 2) × X))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∑ H, if H.Adj a b ∧ H.Adj a c then w H else 0) ≤ B / Fintype.card X := by
  let S : Finset ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) := {a, b, c}
  have hcard : S.card = 3 := by simp [S, hab, hac, hbc]
  have hh := cyclic_graph_event_load_bound w hw hs B hB hn hb S
    (by rw [hcard]; omega) (by rw [hcard]; omega)
    (fun H => H.Adj a b ∧ H.Adj a c) (by
      intro f hf v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact (cyclicSelection_adj_forces f _ _ hf.1).1
      · exact (cyclicSelection_adj_forces f _ _ hf.1).2
      · exact (cyclicSelection_adj_forces f _ _ hf.2).2)
  simp only [hcard, show 3 - 2 = 1 from rfl, pow_one] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro H _
  split_ifs <;> rfl

theorem cyclic_graph_disjoint_pair_load {k : ℕ} {X : Type*}
    [Fintype X] [DecidableEq X]
    (w : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) → ℝ)
    (hw : ∀ H, 0 ≤ w H)
    (hs : ∀ H, 0 < w H → H ∈ Set.range (cyclicSelectionGraph (k := k) (X := X)))
    (B : ℝ) (hB : 0 ≤ B) (hn : 0 < Fintype.card X)
    (hb : ∀ f, w (cyclicSelectionGraph f) ≤ B / (Fintype.card X : ℝ) ^ (2 * k + 2))
    (a b c d : (Fin (k + 2) × X) ⊕ (Fin (k + 2) × X))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∑ H, if H.Adj a b ∧ H.Adj c d then w H else 0) ≤
      B / (Fintype.card X : ℝ) ^ 2 := by
  let S : Finset ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × X)) := {a, b, c, d}
  have hcard : S.card = 4 := by simp [S, hab, hac, had, hbc, hbd, hcd]
  have hh := cyclic_graph_event_load_bound w hw hs B hB hn hb S
    (by rw [hcard]; omega) (by rw [hcard]; omega)
    (fun H => H.Adj a b ∧ H.Adj c d) (by
      intro f hf v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact (cyclicSelection_adj_forces f _ _ hf.1).1
      · exact (cyclicSelection_adj_forces f _ _ hf.1).2
      · exact (cyclicSelection_adj_forces f _ _ hf.2).1
      · exact (cyclicSelection_adj_forces f _ _ hf.2).2)
  simp only [hcard, show 4 - 2 = 2 from rfl] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro H _
  split_ifs <;> rfl

end Oberwolfach
