module

public import Oberwolfach.CommonEvents
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! Medians and a bounded truncation estimate for a finite probability law. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_congr
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (A B : Ω → Prop)
    (h : ∀ ω,A ω ↔ B ω) : μ.probability A=μ.probability B :=
  congrArg μ.probability (funext (fun ω=>propext (h ω)))

theorem finiteLaw_exists_median
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (R : Ω → ℝ) :
    ∃ ω : Ω,1/2≤μ.probability (fun x=>R x≤R ω) ∧
      1/2≤μ.probability (fun x=>R ω≤R x) := by
  classical
  letI : Nonempty Ω := finiteLaw_nonempty μ
  obtain ⟨z,_,hz⟩ := Finset.exists_max_image Finset.univ R Finset.univ_nonempty
  have hzall (x : Ω) : R x≤R z := hz x (Finset.mem_univ x)
  have hztop : μ.probability (fun x=>R x≤R z)=1 := by
    unfold FiniteLaw.probability
    simp only [hzall,ite_true]
    exact μ.total
  let S := Finset.univ.filter (fun ω=>1/2≤μ.probability (fun x=>R x≤R ω))
  have hS : S.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hztop];norm_num⟩⟩
  obtain ⟨ω,hω,hmin⟩ := Finset.exists_min_image S R hS
  refine ⟨ω,(Finset.mem_filter.mp hω).2,?_⟩
  have hlt : μ.probability (fun x=>R x<R ω)≤1/2 := by
    let T := Finset.univ.filter (fun x=>R x<R ω)
    by_cases hT : T.Nonempty
    · obtain ⟨y,hy,hmax⟩ := Finset.exists_max_image T R hT
      have hylt : R y<R ω := (Finset.mem_filter.mp hy).2
      have he : μ.probability (fun x=>R x<R ω)=μ.probability (fun x=>R x≤R y) := by
        apply finiteLaw_probability_congr
        intro x
        constructor
        · intro hx
          exact hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
        · exact fun hx=>hx.trans_lt hylt
      rw [he]
      by_contra h
      have hyS : y∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(lt_of_not_ge h).le⟩
      exact (not_le_of_gt hylt) (hmin y hyS)
    · have hn (x : Ω) : ¬R x<R ω := by
        intro hx
        exact hT ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
      unfold FiniteLaw.probability
      simp only [hn,ite_false,Finset.sum_const_zero]
      norm_num
  have hc := finiteLaw_probability_compl μ (fun x=>R x<R ω)
  simp only [not_lt] at hc
  linarith

theorem finiteLaw_expectation_abs_truncate
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {M t : ℝ} (ht : 0≤t) (hM : ∀ ω,|X ω|≤M) :
    μ.expectation (fun ω=>|X ω|)≤t+M*μ.probability (fun ω=>t≤|X ω|) := by
  classical
  have hh : μ.expectation (fun ω=>|X ω|)≤
      μ.expectation (fun ω=>t+(if t≤|X ω| then M else 0)) := by
    apply finiteLaw_expectation_mono
    intro ω
    by_cases h : t≤|X ω|
    · simp only [h,ite_true]
      linarith [hM ω]
    · simp only [h,ite_false,add_zero]
      exact (lt_of_not_ge h).le
  have he : μ.expectation (fun ω=>t+(if t≤|X ω| then M else 0))=
      t+M*μ.probability (fun ω=>t≤|X ω|) := by
    unfold FiniteLaw.expectation FiniteLaw.probability
    rw [Finset.mul_sum]
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,μ.total,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : t≤|X ω| <;> simp [h,mul_comm]
  exact hh.trans_eq he

theorem finiteLaw_abs_expectation_le
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    |μ.expectation X|≤μ.expectation (fun ω=>|X ω|) := by
  unfold FiniteLaw.expectation
  have h := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun ω=>μ.mass ω*X ω)
  simpa only [abs_mul,abs_of_nonneg (μ.nonneg _)] using h

end Oberwolfach
