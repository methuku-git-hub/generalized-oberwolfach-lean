module

public import Oberwolfach.PhysicalResourceDegreeAggregation

@[expose] public section
/-! The degree of a physical resource in the realized candidate family is
the sum of the active typed root-omitted loads in its physical fiber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq B]

theorem physical_sampled_degree_eq_active_root_loads
    (φ:A→B) (R:C→Finset A) (w:C→ℝ) (σ:A→Bool)
    (hinj:∀c,Set.InjOn φ (↑(R c):Set A)) (x:B):
    (∑c,if x∈(R c).image φ ∧ (∀a∈R c,σ a=true) then w c else 0)=
      ∑a∈Finset.univ.filter (fun a=>φ a=x),
        if σ a=true then resourcePatternLoad R w (fun _ _=>true) a σ else 0 :=by
  let wσ:=fun c=>if ∀a∈R c,σ a=true then w c else 0
  have hdegree:=physical_resource_degree_eq_typed_fibers φ R wσ hinj x
  have hleft:(∑c,if x∈(R c).image φ ∧ (∀a∈R c,σ a=true) then w c else 0)=
      ∑c,if x∈(R c).image φ then wσ c else 0:=by
    apply Finset.sum_congr rfl
    intro c _
    by_cases hx:x∈(R c).image φ <;> by_cases hs:∀a∈R c,σ a=true <;> simp [wσ,hx,hs]
  rw [hleft,hdegree]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha:σ a=true
  · simp only [ha,ite_true]
    unfold resourcePatternLoad
    apply Finset.sum_congr rfl
    intro c _
    rw [patternValue_indicator]
    simp only [wσ,Finset.mem_sdiff,Finset.mem_singleton]
    by_cases hm:a∈R c
    · have heq:(∀b∈R c,σ b=true) ↔ ∀b,b∈R c ∧ b≠a→σ b=true := by
        constructor
        · intro hh b hb;exact hh b hb.1
        · intro hh b hb
          by_cases hba:b=a
          · simpa [hba] using ha
          · exact hh b ⟨hb,hba⟩
      simp [hm,heq]
    · simp [hm]
  · simp only [ha,ite_false]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hm:a∈R c
    · have hh:¬(∀b∈R c,σ b=true):=fun h=>ha (h a hm)
      simp [wσ,hm,hh]
    · simp [hm]
end Oberwolfach
