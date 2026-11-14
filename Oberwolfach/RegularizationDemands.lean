module

public import Oberwolfach.RegularizationParameters
public import Oberwolfach.IntervalRandomDemands
public import Oberwolfach.DenseBipartiteCuts

@[expose] public section

/-! The deletion law for a nearly regular dense bipartite adjacency matrix.
The constants precede the error parameter and the order threshold follows it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regularization_demand_totals {V : Type*} [Fintype V]
    (M : V → V → ℕ) (k : ℕ)
    (hl : ∀ x, k ≤ ∑ y, M x y) (hr : ∀ y, k ≤ ∑ x, M x y) :
    ∑ x, ((∑ y, M x y) - k) = ∑ y, ((∑ x, M x y) - k) := by
  calc
    _ = (∑ x, ∑ y, M x y) - ∑ _x : V, k :=
      Finset.sum_tsub_distrib Finset.univ (fun x _ => hl x)
    _ = (∑ y, ∑ x, M x y) - ∑ _y : V, k := by rw [Finset.sum_comm]
    _ = _ := (Finset.sum_tsub_distrib Finset.univ (fun y _ => hr y)).symm

theorem matrix_regularization_deletion_law (β : ℝ) (hβ : 0 < β) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], m₀ ≤ Fintype.card V →
      ∀ (M : V → V → ℕ), (∀ x y, M x y ≤ 1) → ∀ d : ℝ,
      (∀ x, (1 / 2 + β) * Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ)) →
      (∀ y, (1 / 2 + β) * Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ)) →
      (∀ x, d - η * Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ) ∧
        ((∑ y, M x y : ℕ) : ℝ) ≤ d + η * Fintype.card V) →
      (∀ y, d - η * Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ) ∧
        ((∑ x, M x y : ℕ) : ℝ) ≤ d + η * Fintype.card V) →
      let k := ⌊d - Real.sqrt η * Fintype.card V⌋₊
      (∀ x, k ≤ ∑ y, M x y) ∧ (∀ y, k ≤ ∑ x, M x y) ∧
      ∃ ν : FiniteLaw (BipartiteEdges M → Bool),
        (∀ D, 0 < ν.mass D →
          (∀ x, (∑ e, if e.1 = x ∧ D e = true then (1 : ℕ) else 0) =
            (∑ y, M x y) - k) ∧
          (∀ y, (∑ e, if e.2.1 = y ∧ D e = true then (1 : ℕ) else 0) =
            (∑ x, M x y) - k)) ∧
        (∀ e, ν.probability (fun D => D e = true) ≤ C * Real.sqrt η) := by
  obtain ⟨δ, h, C, η₀, hδ, hδ8, hh, hhβ, hC, hCeq, hη₀, hsmall⟩ :=
    regularization_constants β hβ
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro η hη hηsmall
  obtain ⟨hs, hs4, hsd, hp, hp1⟩ := hsmall η hη hηsmall
  obtain ⟨m₀, _, hm₀⟩ := regularization_order_threshold η hη
  refine ⟨m₀, ?_⟩
  intro V _ _ hm M hM d hleft hright hnearleft hnearright
  obtain ⟨hn, hnlarge⟩ := hm₀ _ hm
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hηsq : η = (Real.sqrt η) ^ 2 := (Real.sq_sqrt hη.le).symm
  have hηs : η ≤ Real.sqrt η := by nlinarith
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
  have harg : 0 ≤ d - Real.sqrt η * Fintype.card V :=
    regularization_floor_argument hn' hβ.le hs.le hs4 hηsq
      (hleft v) (hnearleft v).2
  let k := ⌊d - Real.sqrt η * Fintype.card V⌋₊
  have hfl (x : V) := regularization_floor_demand (∑ y, M x y)
    hn' harg hηs hnlarge (hnearleft x)
  have hfr (y : V) := regularization_floor_demand (∑ x, M x y)
    hn' harg hηs hnlarge (hnearright y)
  refine ⟨fun x => (hfl x).1, fun y => (hfr y).1, ?_⟩
  have hscale := regularization_relative_scale hs hηsq hδ hδ8 hsd
  have hcap := regularization_capacity_scale hs hs4 hηsq hh hCeq
  have result := interval_random_demands (fun e : BipartiteEdges M => e.1)
    (fun e : BipartiteEdges M => e.2.1)
    (fun x => (∑ y, M x y) - k) (fun y => (∑ x, M x y) - k)
    ((Real.sqrt η - η) * Fintype.card V)
    ((Real.sqrt η + 2 * η) * Fintype.card V) δ h (C * Real.sqrt η)
    hn (mul_pos hscale.1 hn') hp hp1 hδ.le (by linarith)
    (by nlinarith [mul_le_mul_of_nonneg_right hscale.2 hn'.le])
    (by nlinarith [mul_le_mul_of_nonneg_right hcap hn'.le])
    (fun x => (hfl x).2) (fun y => (hfr y).2)
    (regularization_demand_totals M k (fun x => (hfl x).1) (fun y => (hfr y).1))
    (matrixEdges_normalized_large_cuts M hM β δ h hn hhβ hleft hright)
  exact result

end Oberwolfach
