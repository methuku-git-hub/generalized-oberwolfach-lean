module

public import Oberwolfach.CycleCopies
public import Oberwolfach.IntervalPathWeights

@[expose] public section

/-! Fractional decompositions are weights on actual subgraphs, rather than
on descriptions that might represent the same subgraph more than once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def HasFractionalDecomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) : Prop :=
  ∃ w : SimpleGraph V → ℝ,
    (∀ H, 0 ≤ w H) ∧
    (∀ H, 0 < w H → H ≤ G ∧ P H) ∧
    (∀ u v, (∑ H, if H.Adj u v then w H else 0) = if G.Adj u v then 1 else 0)

def IsEmbeddedCycle {V : Type*} (H : SimpleGraph V) (r : ℕ) : Prop :=
  3 ≤ r ∧ ∃ f : Fin r ↪ V, H = (SimpleGraph.cycleGraph r).map f

theorem isEmbeddedCycle_iff_isCycleCopy {n r : ℕ} (H : SimpleGraph (Fin n)) :
    IsEmbeddedCycle H r ↔ IsCycleCopy H r := (isCycleCopy_iff_map H).symm

def indexedFractionalWeight {V Ω : Type*} [Fintype Ω]
    (C : Ω → SimpleGraph V) (ω : Ω → ℝ) (H : SimpleGraph V) : ℝ :=
  ∑ a, if C a = H then ω a else 0

theorem indexed_fractional_weight_properties {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (C : Ω → SimpleGraph V) (ω : Ω → ℝ)
    (hω : ∀ a, 0 ≤ ω a)
    (hs : ∀ a, 0 < ω a → C a ≤ G ∧ P (C a))
    (he : ∀ u v, (∑ a, if (C a).Adj u v then ω a else 0) =
      if G.Adj u v then 1 else 0) :
    (∀ H, 0 ≤ indexedFractionalWeight C ω H) ∧
    (∀ H, 0 < indexedFractionalWeight C ω H → H ≤ G ∧ P H) ∧
    (∀ u v, (∑ H, if H.Adj u v then indexedFractionalWeight C ω H else 0) =
      if G.Adj u v then 1 else 0) := by
  let w (H : SimpleGraph V) := ∑ a, if C a = H then ω a else 0
  change (∀ H, 0 ≤ w H) ∧ (∀ H, 0 < w H → H ≤ G ∧ P H) ∧
    (∀ u v, (∑ H, if H.Adj u v then w H else 0) = if G.Adj u v then 1 else 0)
  refine ⟨?_, ?_, ?_⟩
  · intro H
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact hω a
    · exact le_refl _
  · intro H hH
    obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun a (_ : a ∈ Finset.univ) => show 0 ≤ (if C a = H then ω a else 0) by
        split_ifs; exact hω a; exact le_refl _)).mp hH
    split_ifs at ha with hCH
    · rw [← hCH]
      exact hs a ha
    · exact False.elim ((lt_irrefl 0) ha)
  · intro u v
    have hh := finite_marginal_test ω C w (fun _ => rfl)
      (fun H => if H.Adj u v then (1 : ℝ) else 0)
    simp only [mul_ite, mul_one, mul_zero] at hh
    rw [← hh]
    exact he u v

theorem fractionalDecomposition_of_indexed {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (C : Ω → SimpleGraph V) (ω : Ω → ℝ)
    (hω : ∀ a, 0 ≤ ω a)
    (hs : ∀ a, 0 < ω a → C a ≤ G ∧ P (C a))
    (he : ∀ u v, (∑ a, if (C a).Adj u v then ω a else 0) =
      if G.Adj u v then 1 else 0) :
    HasFractionalDecomposition G P := by
  exact ⟨indexedFractionalWeight C ω,
    indexed_fractional_weight_properties G P C ω hω hs he⟩

end Oberwolfach
