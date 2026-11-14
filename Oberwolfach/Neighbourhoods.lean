module

public import Mathlib.Tactic

@[expose] public section

/-! Finite neighbourhood stability: manuscript Lemma `lem:pr:rt1-stability`.
The ambient set is fixed, and the deletion may be chosen after both families. -/
set_option autoImplicit false
open scoped BigOperators
namespace Oberwolfach

noncomputable def common {V I : Type*} (A : Finset V) (J : Finset I)
    (N : I → Finset V) : Finset V := by
  classical
  exact A.filter (fun v => ∀ j ∈ J, v ∈ N j)

noncomputable def changed {V : Type*} (A B : Finset V) : Finset V := by
  classical
  exact (A \ B) ∪ (B \ A)

theorem card_difference_le_changed {V : Type*} (A B : Finset V) :
    |(A.card : ℝ) - B.card| ≤ (changed A B).card := by
  classical
  have ha : A ⊆ B ∪ changed A B := by
    intro v hv
    by_cases h : v ∈ B
    · exact Finset.mem_union_left _ h
    · simp [changed, hv, h]
  have hb : B ⊆ A ∪ changed A B := by
    intro v hv
    by_cases h : v ∈ A
    · exact Finset.mem_union_left _ h
    · simp [changed, hv, h]
  have hca := (Finset.card_le_card ha).trans (Finset.card_union_le _ _)
  have hcb := (Finset.card_le_card hb).trans (Finset.card_union_le _ _)
  have hca' : (A.card : ℝ) ≤ B.card + (changed A B).card := by exact_mod_cast hca
  have hcb' : (B.card : ℝ) ≤ A.card + (changed A B).card := by exact_mod_cast hcb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem common_changed_subset {V I : Type*} [DecidableEq V] (A : Finset V) (J : Finset I)
    (N N' : I → Finset V) :
    changed (common A J N) (common A J N') ⊆
      J.biUnion (fun j => changed (N j) (N' j)) := by
  classical
  intro v hv
  have hd : (v ∈ common A J N ∧ v ∉ common A J N') ∨
      (v ∈ common A J N' ∧ v ∉ common A J N) := by
    simpa [changed] using hv
  rcases hd with ⟨h, h'⟩ | ⟨h, h'⟩
  · simp only [common, Finset.mem_filter] at h h'
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ J, v ∉ N' j := by
      by_contra hh
      push Not at hh
      exact h' ⟨h.1, hh⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [changed, h.2 j hj, hj']⟩
  · simp only [common, Finset.mem_filter] at h h'
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ J, v ∉ N j := by
      by_contra hh
      push Not at hh
      exact h' ⟨h.1, hh⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [changed, h.2 j hj, hj']⟩

theorem neighbourhood_stability {V I : Type*} (A : Finset V) (J : Finset I)
    (N N' : I → Finset V) (b : ℝ)
    (hb : ∀ j ∈ J, ((changed (N j) (N' j)).card : ℝ) ≤ b) :
    |((common A J N').card : ℝ) - (common A J N).card| ≤ J.card * b := by
  classical
  have hcard : (changed (common A J N) (common A J N')).card ≤
      ∑ j ∈ J, (changed (N j) (N' j)).card :=
    (Finset.card_le_card (common_changed_subset A J N N')).trans Finset.card_biUnion_le
  have hcard' : ((changed (common A J N) (common A J N')).card : ℝ) ≤
      ∑ j ∈ J, ((changed (N j) (N' j)).card : ℝ) := by exact_mod_cast hcard
  have hsum : (∑ j ∈ J, ((changed (N j) (N' j)).card : ℝ)) ≤ J.card * b := by
    calc
      _ ≤ ∑ j ∈ J, b := Finset.sum_le_sum hb
      _ = _ := by simp
  rw [abs_sub_comm]
  exact (card_difference_le_changed _ _).trans (hcard'.trans hsum)

theorem target_stability {x y μ e t : ℝ}
    (hxy : |y - x| ≤ t) (hx : |x - μ| ≤ e) : |y - μ| ≤ e + t := by
  calc
    |y - μ| = |(y - x) + (x - μ)| := by congr 1; ring
    _ ≤ |y - x| + |x - μ| := abs_add_le _ _
    _ ≤ e + t := by linarith

theorem deletion_lower_bound {V : Type*} [DecidableEq V] (B D : Finset V) {μ e : ℝ}
    (h : |(B.card : ℝ) - μ| ≤ e) :
    μ - e - D.card ≤ ((B \ D).card : ℝ) := by
  classical
  have hc : (B.card : ℝ) ≤ (B \ D).card + D.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := B) (t := D))
  have he := (abs_le.mp h).1
  linarith

/-- Full conclusion, with no requirement that D be fixed before N'. -/
theorem neighbourhood_stability_with_deletion {V I : Type*} [DecidableEq V]
    (A : Finset V) (J : Finset I) (N N' : I → Finset V) (b μ e : ℝ)
    (hb : ∀ j ∈ J, ((changed (N j) (N' j)).card : ℝ) ≤ b)
    (he : |((common A J N).card : ℝ) - μ| ≤ e) (D : Finset V) :
    |((common A J N').card : ℝ) - μ| ≤ e + J.card * b ∧
    μ - e - J.card * b - D.card ≤ ((common A J N' \ D).card : ℝ) := by
  have h := target_stability (neighbourhood_stability A J N N' b hb) he
  refine ⟨h, ?_⟩
  convert deletion_lower_bound (common A J N') D h using 1; ring

end Oberwolfach
