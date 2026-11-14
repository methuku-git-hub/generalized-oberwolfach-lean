module

public import Oberwolfach.ResourceDecompositionCounts
public import Oberwolfach.FiniteSignedAverages

@[expose] public section

/-! Signed incidence identities obtained from the two actual factors
of an absorber. All cycle identifiers are retained in the averages. -/
set_option autoImplicit false
set_option maxHeartbeats 2300000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C J : Type*} [DecidableEq V] [DecidableEq C] [Fintype C] [Fintype J]

def absorberTrade (M₀ M₁ : Finset C) (C₀ : C) : ℝ :=
  (if C₀∈M₁ then (1:ℝ) else 0)-(if C₀∈M₀ then 1 else 0)

theorem absorberTrade_incidence (R : C → Finset V) (X A : Finset V) (hXA : Disjoint A X)
    (M₀ M₁ : Finset C)
    (h₀ : ∀ a∈M₀,∀ b∈M₀,a≠b → Disjoint (R a) (R b)) (he₀ : M₀.biUnion R=A)
    (h₁ : ∀ a∈M₁,∀ b∈M₁,a≠b → Disjoint (R a) (R b)) (he₁ : M₁.biUnion R=A∪X) (v : V) :
    (∑ C₀,if v∈R C₀ then absorberTrade M₀ M₁ C₀ else 0)=if v∈X then 1 else 0 := by
  have heq (C₀ : C) : (if v∈R C₀ then absorberTrade M₀ M₁ C₀ else 0)=
      (if v∈R C₀ then (if C₀∈M₁ then (1:ℝ) else 0) else 0)-
      (if v∈R C₀ then (if C₀∈M₀ then (1:ℝ) else 0) else 0) := by
    by_cases h : v∈R C₀ <;> simp [absorberTrade,h]
  simp_rw [heq,Finset.sum_sub_distrib]
  rw [resource_decomposition_indicator_weight R M₁ (A∪X) h₁ he₁ v,
    resource_decomposition_indicator_weight R M₀ A h₀ he₀ v]
  by_cases ha : v∈A <;> by_cases hx : v∈X
  · exact ((Finset.disjoint_left.mp hXA) ha hx).elim
  all_goals simp [ha,hx]

theorem absorberTrade_abs_le (M₀ M₁ : Finset C) (C₀ : C) :
    |absorberTrade M₀ M₁ C₀| ≤ (if C₀∈M₀ then (1:ℝ) else 0)+(if C₀∈M₁ then 1 else 0) := by
  by_cases h₀ : C₀∈M₀ <;> by_cases h₁ : C₀∈M₁ <;> norm_num [absorberTrade,h₀,h₁]

theorem averaged_absorber_trade_incidence (R : C → Finset V) (X : Finset V)
    (hJ : 0 < Fintype.card J) (A : J → Finset V) (M₀ M₁ : J → Finset C)
    (hXA : ∀ j,Disjoint (A j) X)
    (h₀ : ∀ j,∀ a∈M₀ j,∀ b∈M₀ j,a≠b → Disjoint (R a) (R b))
    (he₀ : ∀ j,(M₀ j).biUnion R=A j)
    (h₁ : ∀ j,∀ a∈M₁ j,∀ b∈M₁ j,a≠b → Disjoint (R a) (R b))
    (he₁ : ∀ j,(M₁ j).biUnion R=A j∪X) (v : V) :
    (∑ C₀,if v∈R C₀ then finiteSignedAverage (fun j => absorberTrade (M₀ j) (M₁ j)) C₀ else 0)=
      if v∈X then 1 else 0 := by
  have hh := finiteSignedAverage_indicator_constant hJ (fun j => absorberTrade (M₀ j) (M₁ j))
    (fun C₀ => v∈R C₀) (if v∈X then (1:ℝ) else 0) (by
      intro j
      convert absorberTrade_incidence R X (A j) (hXA j) (M₀ j) (M₁ j) (h₀ j) (he₀ j) (h₁ j) (he₁ j) v using 1 <;> congr!)
  convert hh using 1 <;> congr!

theorem averaged_absorber_trade_bound (M₀ M₁ : J → Finset C) (C₀ : C) :
    |finiteSignedAverage (fun j => absorberTrade (M₀ j) (M₁ j)) C₀| ≤
      (((Finset.univ.filter (fun j => C₀∈M₀ j)).card:ℝ)+
        ((Finset.univ.filter (fun j => C₀∈M₁ j)).card:ℝ))/Fintype.card J := by
  apply (finiteSignedAverage_abs_le _ C₀).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ j,((if C₀∈M₀ j then (1:ℝ) else 0)+(if C₀∈M₁ j then 1 else 0)) :=
      Finset.sum_le_sum (fun j _ => absorberTrade_abs_le (M₀ j) (M₁ j) C₀)
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

end Oberwolfach
