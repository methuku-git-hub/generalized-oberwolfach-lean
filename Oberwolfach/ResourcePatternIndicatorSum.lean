module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! An omitted-root pattern load is a sum over the candidates satisfying its test. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A I:Type} [Fintype A] [Fintype I] [DecidableEq A]
theorem resource_pattern_indicator_sum {State:A→Type} (R:I→Finset A) (w:I→ℝ)
    (s:I→∀ a,State a) (e:A) (σ:∀ a,State a) (p:I→Prop)
    (hp:∀ i, (e∈R i ∧ ∀ a∈R i\{e},σ a=s i a)↔p i):
    resourcePatternLoad R w s e σ=∑ i,if p i then w i else 0 := by
  unfold resourcePatternLoad
  apply Finset.sum_congr rfl
  intro i _
  rw [patternValue_indicator]
  simp only [Finset.mem_sdiff,Finset.mem_singleton] at hp ⊢
  by_cases he:e∈R i
  · simp only [he,if_true]
    by_cases ht:∀ a, a∈R i ∧ ¬a=e → σ a=s i a
    · have hpi:p i := (hp i).mp ⟨he,ht⟩
      simp only [hpi,ite_true]
      split_ifs <;> simp_all
    · have hpi:¬p i := fun h => ht ((hp i).mpr h).2
      simp only [hpi,ite_false]
      split_ifs <;> simp_all
  · have hpi:¬p i := fun h=>he ((hp i).mpr h).1
    simp only [he,hpi,ite_false,zero_mul]
end Oberwolfach
