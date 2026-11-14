module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Union bounds for finite linear combinations of centred variables. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_expectation_linear
    {Ω J : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Finset J) (b : J → ℝ) (X : J → Ω → ℝ) :
    μ.expectation (fun ω=>∑ j∈T,b j*X j ω)=∑ j∈T,b j*μ.expectation (X j) := by
  unfold FiniteLaw.expectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem finiteLaw_linear_tail
    {Ω J : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Finset J) (hT : T.Nonempty) (b : J → ℝ) (X : J → Ω → ℝ)
    (hb : ∀ j∈T,|b j|≤1) (t : ℝ) (p : J → ℝ)
    (hp : ∀ j∈T,μ.probability (fun ω=>t≤|X j ω-μ.expectation (X j)|)≤p j) :
    μ.probability (fun ω=>(T.card : ℝ)*t≤
      |(∑ j∈T,b j*X j ω)-μ.expectation (fun ω=>∑ j∈T,b j*X j ω)|)≤
      ∑ j∈T,p j := by
  have hsub (ω : Ω)
      (hω : (T.card : ℝ)*t≤
        |(∑ j∈T,b j*X j ω)-μ.expectation (fun ω=>∑ j∈T,b j*X j ω)|) :
      ∃ j∈T,t≤|X j ω-μ.expectation (X j)| := by
    by_contra hn
    have hsmall (j : J) (hj : j∈T) : |X j ω-μ.expectation (X j)|<t :=
      lt_of_not_ge (fun h=>hn ⟨j,hj,h⟩)
    have he : (∑ j∈T,b j*X j ω)-μ.expectation (fun ω=>∑ j∈T,b j*X j ω)=
        ∑ j∈T,b j*(X j ω-μ.expectation (X j)) := by
      rw [finiteLaw_expectation_linear,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hab : |∑ j∈T,b j*(X j ω-μ.expectation (X j))|<
        (T.card : ℝ)*t := by
      calc
        _ ≤ ∑ j∈T,|b j*(X j ω-μ.expectation (X j))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j∈T,|X j ω-μ.expectation (X j)| := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          simpa using mul_le_mul_of_nonneg_right (hb j hj) (abs_nonneg _)
        _ < ∑ _j∈T,t := Finset.sum_lt_sum_of_nonempty hT hsmall
        _ = _ := by simp
    rw [he] at hω
    exact (not_lt_of_ge hω) hab
  exact ((finiteLaw_probability_mono μ _ _ hsub).trans
    (finiteLaw_union_bound μ T _)).trans (Finset.sum_le_sum hp)

end Oberwolfach
