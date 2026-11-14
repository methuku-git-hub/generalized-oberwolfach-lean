module

public import Oberwolfach.FiniteChernoff
public import Oberwolfach.EdgeRetention
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Independent selection of a finite family of configurations. All
compatibility sets and intersecting pairs are fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_nonnegative_markov {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (X : Ω → ℝ) (hX : ∀ ω,0 ≤ X ω) (t : ℝ) (ht : 0 < t) :
    μ.probability (fun ω => t ≤ X ω) ≤ μ.expectation X/t := by
  apply (le_div_iff₀ ht).mpr
  unfold FiniteLaw.probability FiniteLaw.expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : t ≤ X ω
  · simp only [h,ite_true]
    exact mul_le_mul_of_nonneg_left h (μ.nonneg ω)
  · simp only [h,ite_false,zero_mul]
    exact mul_nonneg (μ.nonneg ω) (hX ω)

variable {C : Type*} [Fintype C] [DecidableEq C]

def selectedConfigurationCount (S : Finset C) (σ : C → Bool) : ℕ :=
  (S.filter (fun c => σ c=true)).card

theorem selectedConfigurationCount_sum (S : Finset C) (σ : C → Bool) :
    (selectedConfigurationCount S σ:ℝ)=∑ c : C,if c∈S ∧ σ c=true then (1:ℝ) else 0 := by
  simp only [selectedConfigurationCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp only [← Finset.sum_filter]
  congr 1
  ext c
  simp

theorem selectedConfigurationCount_mean (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset C) :
    (FiniteLaw.pi (fun _ : C => FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ => (selectedConfigurationCount S σ:ℝ))=p*S.card := by
  simp_rw [selectedConfigurationCount_sum]
  rw [finiteLaw_pi_expectation_sum (fun _ : C => FiniteLaw.retentionCoin p hp hp1)
    (fun c b => if c∈S ∧ b=true then (1:ℝ) else 0)]
  have hx (c : C) : (FiniteLaw.retentionCoin p hp hp1).expectation
      (fun b => if c∈S ∧ b=true then (1:ℝ) else 0)=if c∈S then p else 0 := by
    by_cases h : c∈S <;> simp [FiniteLaw.expectation,FiniteLaw.retentionCoin,Fintype.sum_bool,h]
  simp_rw [hx]
  simp [mul_comm]

theorem selectedConfigurationCount_lower_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset C) :
    (FiniteLaw.pi (fun _ : C => FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ => (selectedConfigurationCount S σ:ℝ)<p*S.card/2) ≤
      2*Real.exp (-p*S.card/12) := by
  let μ := FiniteLaw.pi (fun _ : C => FiniteLaw.retentionCoin p hp hp1)
  have hm := selectedConfigurationCount_mean p hp hp1 S
  have hC := finiteLaw_independent_chernoff (fun _ : C => FiniteLaw.retentionCoin p hp hp1)
    (fun c b => if c∈S ∧ b=true then (1:ℝ) else 0)
    (by intro c b;split_ifs <;> norm_num) (ε:=1/2) (by norm_num) (by norm_num)
  simp only [← selectedConfigurationCount_sum] at hC
  rw [hm] at hC
  have hmono := finiteLaw_probability_mono μ
    (fun σ => (selectedConfigurationCount S σ:ℝ)<p*S.card/2)
    (fun σ => (1/2)*(p*S.card) ≤ |(selectedConfigurationCount S σ:ℝ)-p*S.card|)
    (by intro σ h;have hh := neg_le_abs ((selectedConfigurationCount S σ:ℝ)-p*S.card);linarith)
  exact hmono.trans (by convert hC using 1 <;> congr 2 <;> ring)

def selectedConfigurationPairs (P : Finset (C×C)) (σ : C → Bool) : ℕ :=
  (P.filter (fun z => σ z.1=true ∧ σ z.2=true)).card

theorem selectedConfigurationPairs_mean (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset (C×C)) (hP : ∀ z∈P,z.1≠z.2) :
    (FiniteLaw.pi (fun _ : C => FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ => (selectedConfigurationPairs P σ:ℝ))=p^2*P.card := by
  let μ := fun _ : C => FiniteLaw.retentionCoin p hp hp1
  have heq (σ : C → Bool) : (selectedConfigurationPairs P σ:ℝ)=
      ∑ z∈P,patternValue {z.1,z.2} (fun _ => true) σ := by
    simp only [selectedConfigurationPairs,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [patternValue,Finset.prod_insert (Finset.notMem_singleton.mpr (hP z hz)),Finset.prod_singleton]
    by_cases h₁ : σ z.1=true <;> by_cases h₂ : σ z.2=true <;> simp [h₁,h₂]
  have hm (z : C×C) (hz : z∈P) :
      (FiniteLaw.pi μ).expectation (patternValue {z.1,z.2} (fun _ => true))=p^2 := by
    rw [finiteLaw_expectation_pattern]
    simp only [Finset.prod_insert (Finset.notMem_singleton.mpr (hP z hz)),Finset.prod_singleton,μ,
      FiniteLaw.retentionCoin,Bool.true_eq,ite_true]
    ring
  simp_rw [heq]
  unfold FiniteLaw.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ _z∈P,p^2 := Finset.sum_congr rfl hm
    _ = _ := by simp [mul_comm]

end Oberwolfach
