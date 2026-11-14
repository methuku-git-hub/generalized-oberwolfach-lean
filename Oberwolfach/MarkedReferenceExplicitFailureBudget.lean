module

public import Oberwolfach.MarkedReferenceJointFailureBudget

@[expose] public section
/-! One explicit positive choice of all fixed failure parameters and a
numerical order bound for the two exponent-one error terms. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_fixed_failure_one_hundredth:
    markedReferenceFixedFailure (1/100) (1/100) (1/100) (1/100) (1/100) (1/100) (1/100) (1/100)=1/10:=by
  norm_num [markedReferenceFixedFailure]

theorem marked_reference_explicit_error_positive (n:ℕ) (hn:16≤n):
    0<1-(1/10:ℝ)-5*(n:ℝ)^(-(1:ℝ))-9*(n:ℝ)^(-(1:ℝ)):=by
  have hnR:(16:ℝ)≤n:=by exact_mod_cast hn
  have hnpos:(0:ℝ)<n:=by linarith
  have hfrac:(14:ℝ)/n<9/10:=by
    apply (div_lt_iff₀ hnpos).2
    linarith
  rw [Real.rpow_neg hnpos.le,Real.rpow_one]
  rw [show (n:ℝ)⁻¹=1/n by ring]
  have hid:(5*(1/(n:ℝ))+9*(1/(n:ℝ)):ℝ)=14/n:=by ring
  rw [←hid] at hfrac
  linarith

theorem marked_reference_explicit_positive_mass
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop) (n:ℕ) (hn:16≤n)
    (hE:1-(1/10:ℝ)-5*(n:ℝ)^(-(1:ℝ))-9*(n:ℝ)^(-(1:ℝ))≤μ.probability E):
    ∃ ω,E ω ∧ 0<μ.mass ω:=by
  have hprob:0<μ.probability E:=(marked_reference_explicit_error_positive n hn).trans_le hE
  unfold FiniteLaw.probability at hprob
  have hnonneg:∀ ω∈(Finset.univ:Finset Ω),0≤(if E ω then μ.mass ω else 0):=by
    intro ω _;split_ifs
    · exact μ.nonneg ω
    · norm_num
  obtain ⟨ω,_,hω⟩:=(Finset.sum_pos_iff_of_nonneg hnonneg).mp hprob
  by_cases h:E ω
  · exact ⟨ω,h,by simpa [h] using hω⟩
  · simp [h] at hω
end Oberwolfach
