module

public import Oberwolfach.AveragedDecompositions
public import Oberwolfach.GoodAveraging
public import Oberwolfach.HypergraphWeightMoments

@[expose] public section

/-! Exact vertex-load correction by signed trades, with a quantitative
bound on the change of each fixed cycle coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_abs_expectation_bound {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) : |μ.expectation f| ≤ μ.expectation (fun ω => |f ω|) := by
  calc
    _ ≤ ∑ ω,|μ.mass ω*f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,abs_of_nonneg (μ.nonneg _),FiniteLaw.expectation]

variable {Ω V C : Type*} [Fintype Ω] [Fintype C] [DecidableEq V]

def correctedTradeWeight (μ : FiniteLaw Ω) (w : C → ℝ) (t : Ω → ℝ) (T : Ω → C → ℝ) (c : C) : ℝ :=
  w c+μ.expectation (fun ω => t ω*T ω c)

theorem correctedTradeWeight_exact (μ : FiniteLaw Ω) (R : C → Finset V) (X : Ω → Finset V)
    (w : C → ℝ) (t : Ω → ℝ) (T : Ω → C → ℝ)
    (hT : ∀ ω v,hypergraphWeightedDegree R (T ω) v=if v∈X ω then 1 else 0)
    (ht : ∀ v,μ.expectation (fun ω => t ω*(if v∈X ω then 1 else 0))=1-hypergraphWeightedDegree R w v) :
    ∀ v,hypergraphWeightedDegree R (correctedTradeWeight μ w t T) v=1 := by
  intro v
  have havg := averagedWeight_incidence μ (fun ω c => t ω*T ω c) 1 (fun c => v∈R c)
  simp only [averagedWeight,div_one] at havg
  have hpoint (ω : Ω) : (∑ c,if v∈R c then t ω*T ω c else 0)=
      t ω*hypergraphWeightedDegree R (T ω) v := by
    simp only [hypergraphWeightedDegree,Finset.mul_sum,mul_ite,mul_zero]
  have havg' : (∑ c,if v∈R c then μ.expectation (fun ω => t ω*T ω c) else 0)=
      1-hypergraphWeightedDegree R w v := by
    calc
      _ = μ.expectation (fun ω => ∑ c,if v∈R c then t ω*T ω c else 0) := by
        convert havg using 1 <;> congr!
      _ = μ.expectation (fun ω => t ω*(if v∈X ω then 1 else 0)) := by
        apply congrArg μ.expectation
        funext ω
        rw [hpoint,hT]
      _ = _ := ht v
  have heq (c : C) : (if v∈R c then correctedTradeWeight μ w t T c else 0)=
      (if v∈R c then w c else 0)+(if v∈R c then μ.expectation (fun ω => t ω*T ω c) else 0) := by
    by_cases hc : v∈R c <;> simp [hc,correctedTradeWeight]
  unfold hypergraphWeightedDegree
  simp_rw [heq,Finset.sum_add_distrib]
  rw [havg']
  change hypergraphWeightedDegree R w v+(1-hypergraphWeightedDegree R w v)=1
  ring

theorem correctedTradeWeight_difference (μ : FiniteLaw Ω) (w : C → ℝ) (t : Ω → ℝ)
    (T : Ω → C → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (ht : ∀ ω,|t ω| ≤ A) (hT : ∀ c,μ.expectation (fun ω => |T ω c|) ≤ B) (c : C) :
    |correctedTradeWeight μ w t T c-w c| ≤ A*B := by
  simp only [correctedTradeWeight,add_sub_cancel_left]
  calc
    _ ≤ μ.expectation (fun ω => |t ω*T ω c|) := finiteLaw_abs_expectation_bound μ _
    _ ≤ μ.expectation (fun ω => A*|T ω c|) := finiteLaw_expectation_mono μ _ _
      (by intro ω;rw [abs_mul];exact mul_le_mul_of_nonneg_right (ht ω) (abs_nonneg _))
    _ = A*μ.expectation (fun ω => |T ω c|) := finiteLaw_expectation_const_mul μ A _
    _ ≤ A*B := mul_le_mul_of_nonneg_left (hT c) hA

theorem finiteLaw_trade_bound_from_hit_probability (μ : FiniteLaw Ω)
    (T : Ω → C → ℝ) (hit : C → Ω → Prop) (L U κ : ℝ) (hU : 0 ≤ U)
    (hT : ∀ ω c,|T ω c| ≤ L+(if hit c ω then U else 0))
    (hhit : ∀ c,μ.probability (hit c) ≤ κ) (c : C) :
    μ.expectation (fun ω => |T ω c|) ≤ L+U*κ := by
  have hh := finiteLaw_expectation_mono μ _ _ (fun ω => hT ω c)
  have he : μ.expectation (fun ω => L+(if hit c ω then U else 0))=L+U*μ.probability (hit c) := by
    simp only [FiniteLaw.expectation,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,μ.total,one_mul]
    congr 1
    exact finiteLaw_expectation_indicator_value μ (hit c) U
  rw [he] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hhit c) hU))

theorem correctedTradeWeight_two_sided (μ : FiniteLaw Ω) (w : C → ℝ) (t : Ω → ℝ)
    (T : Ω → C → ℝ) (A B l u : ℝ) (hA : 0 ≤ A)
    (ht : ∀ ω,|t ω| ≤ A) (hT : ∀ c,μ.expectation (fun ω => |T ω c|) ≤ B)
    (hw : ∀ c,l ≤ w c ∧ w c ≤ u) (hsmall : A*B ≤ l/2) (c : C) :
    l/2 ≤ correctedTradeWeight μ w t T c ∧ correctedTradeWeight μ w t T c ≤ u+l/2 := by
  have hh := correctedTradeWeight_difference μ w t T A B hA ht hT c
  have hb := abs_le.mp hh
  constructor <;> linarith [hw c]

end Oberwolfach
