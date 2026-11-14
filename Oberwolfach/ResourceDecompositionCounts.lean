module

public import Oberwolfach.ResourceDecompositions
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! Exact multiplicities in a decomposition. These convert an actual
edge partition into unit edge loads; they do not infer a partition from
fractional weights. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W : Type*} [DecidableEq E] [DecidableEq W]

theorem resource_decomposition_indicator (R : W → Finset E) (M : Finset W) (S : Finset E)
    (hM : ∀ a∈M, ∀ b∈M, a≠b → Disjoint (R a) (R b)) (hS : M.biUnion R=S) (e : E) :
    (∑ w∈M, if e∈R w then (1:ℝ) else 0)=if e∈S then 1 else 0 := by
  by_cases he : e∈S
  · rw [if_pos he]
    rw [← hS] at he
    obtain ⟨a,ha,hea⟩ := Finset.mem_biUnion.mp he
    have hh : (∑ w∈M, if e∈R w then (1:ℝ) else 0)=if e∈R a then 1 else 0 := by
      apply Finset.sum_eq_single_of_mem a ha
      intro b hb hba
      apply if_neg
      intro heb
      exact (Finset.disjoint_left.mp (hM b hb a ha hba)) heb hea
    simpa only [hea,ite_true] using hh
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro w hw
    apply if_neg
    intro hew
    apply he
    rw [← hS]
    exact Finset.mem_biUnion.mpr ⟨w,hw,hew⟩

theorem resource_decomposition_indicator_weight [Fintype W]
    (R : W → Finset E) (M : Finset W) (S : Finset E)
    (hM : ∀ a∈M, ∀ b∈M, a≠b → Disjoint (R a) (R b)) (hS : M.biUnion R=S) (e : E) :
    (∑ w, if e∈R w then (if w∈M then (1:ℝ) else 0) else 0)=if e∈S then 1 else 0 := by
  calc
    _ = ∑ w, if w∈M then (if e∈R w then (1:ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w∈M <;> by_cases he : e∈R w <;> simp [hw,he]
    _ = ∑ w∈M, if e∈R w then (1:ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    _ = _ := resource_decomposition_indicator R M S hM hS e

end Oberwolfach
