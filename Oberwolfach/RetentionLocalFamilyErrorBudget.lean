module

public import Oberwolfach.RetentionLocalFamilyTailTerm
public import Oberwolfach.FiniteInverseCubeWeightedBudget

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retention_local_family_error_budget
    (d:ℕ) (c δ:ℝ) (hc:0<c) (hδ:0<δ):
    ∃m:ℕ,1≤m ∧ ∀(I:Type) (T:Finset I) (A H:I→ℕ),
    (∀i∈T,m≤A i) → Set.InjOn A T →
    (∀i∈T,(H i:ℝ)≤A i) → (∀i∈T,c*(A i:ℝ)≤H i) →
    (∑i∈T,((H i:ℝ)*(1/(A i:ℝ)^6)+(A i:ℝ)*((d+1:ℕ)*(1/(H i:ℝ)^6))))≤δ:=by
  let C:ℝ:=1+((d+1:ℕ):ℝ)/c^6
  have hC:0≤C:=by dsimp [C];positivity
  obtain ⟨m,hm,hbudget⟩:=inverse_cube_distinct_scales_weighted_budget C δ hC hδ
  refine ⟨m,hm,?_⟩
  intro I T A H hmin hinj hHup hHlo
  have hEach:∀i∈T,(H i:ℝ)*(1/(A i:ℝ)^6)+(A i:ℝ)*((d+1:ℕ)*(1/(H i:ℝ)^6))≤C*(1/(A i:ℝ)^3):=by
    intro i hi
    have hh:=retention_local_family_tail_term (A i) (H i) d c hc (le_trans hm (hmin i hi)) (hHup i hi) (hHlo i hi)
    dsimp only [C]
    convert hh using 1 <;> ring
  calc
    _ ≤ ∑i∈T,C*(1/(A i:ℝ)^3):=Finset.sum_le_sum hEach
    _ = C*(∑i∈T,(1:ℝ)/(A i:ℝ)^3):=by rw [Finset.mul_sum]
    _ ≤ δ:=hbudget I T A hmin hinj
end Oberwolfach
