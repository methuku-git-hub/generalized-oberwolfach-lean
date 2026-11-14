module

public import Oberwolfach.ProfileSamplingProbabilities
public import Oberwolfach.ChooseRatio
public import Oberwolfach.SigmaClassCounts

@[expose] public section

/-! Fixed-size class samples and a fixed family of forbidden pairs.
The expected collision bound uses the actual without-replacement law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_subset_inclusion_upper (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρm : ∀ i,(m i:ℝ)/Fintype.card (V i) ≤ ρ) (A : Finset (Σ i,V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => A⊆profileRootSet σ) ≤ ρ^A.card := by
  rw [profile_subset_inclusion_probability m hm]
  let a := fun i => (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card
  have ha : ∀ i,a i ≤ Fintype.card (V i) := fun i => Finset.card_le_univ _
  have hsum : ∑ i,a i=A.card := (sigma_finset_card A).symm
  calc
    _ ≤ ∏ i,ρ^(a i) := by
      apply Finset.prod_le_prod₀
      · intro i _;positivity
      · intro i _
        exact (choose_ratio_le_power (hm i) (ha i)).trans
          (pow_le_pow_left₀ (by positivity) (hρm i) _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,hsum]

theorem profile_pair_inclusion_upper (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρm : ∀ i,(m i:ℝ)/Fintype.card (V i) ≤ ρ) (x y : Σ i,V i) (hxy : x≠y) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => x∈profileRootSet σ ∧ y∈profileRootSet σ) ≤ ρ^2 := by
  have hh := profile_subset_inclusion_upper m hm ρ hρ hρm {x,y}
  simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.card_pair hxy] using hh

theorem profile_forbidden_pairs_expectation (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρm : ∀ i,(m i:ℝ)/Fintype.card (V i) ≤ ρ)
    (E : Finset ((Σ i,V i)×(Σ i,V i))) (hE : ∀ e∈E,e.1≠e.2) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
      (fun σ => ((E.filter (fun e => e.1∈profileRootSet σ ∧ e.2∈profileRootSet σ)).card:ℝ)) ≤
      (E.card:ℝ)*ρ^2 := by
  calc
    _ = ∑ e∈E,(FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
        (fun σ => e.1∈profileRootSet σ ∧ e.2∈profileRootSet σ) := by
      convert finiteLaw_expectation_count
        (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))) E
        (fun e σ => e.1∈profileRootSet σ ∧ e.2∈profileRootSet σ) using 1 <;> congr!
    _ ≤ ∑ _e∈E,ρ^2 := Finset.sum_le_sum (fun e he => profile_pair_inclusion_upper m hm ρ hρ hρm e.1 e.2 (hE e he))
    _ = _ := by simp

theorem profile_forbidden_pairs_probability (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρm : ∀ i,(m i:ℝ)/Fintype.card (V i) ≤ ρ)
    (E : Finset ((Σ i,V i)×(Σ i,V i))) (hE : ∀ e∈E,e.1≠e.2) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => ∃ e∈E,e.1∈profileRootSet σ ∧ e.2∈profileRootSet σ) ≤
      (E.card:ℝ)*ρ^2 := by
  apply (finiteLaw_union_bound _ E (fun e σ => e.1∈profileRootSet σ ∧ e.2∈profileRootSet σ)).trans
  calc
    _ ≤ ∑ _e∈E,ρ^2 := Finset.sum_le_sum (fun e he => profile_pair_inclusion_upper m hm ρ hρ hρm e.1 e.2 (hE e he))
    _ = _ := by simp

end Oberwolfach
