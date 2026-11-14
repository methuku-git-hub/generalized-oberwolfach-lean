module

public import Oberwolfach.FractionalCycleIncidence
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Averaging fractional decompositions of successful sampled subgraphs.
The failed-sample loss and the support probability are kept explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fractional_cycle_sample_weights {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (J : Ω → SimpleGraph V) (r : ℕ) (good : Ω → Prop)
    (hf : ∀ ω,good ω → HasFractionalDecomposition (J ω) (fun C => IsEmbeddedCycle C r)) :
    ∃ w : Ω → SimpleGraph V → ℝ,
      (∀ ω C,0≤w ω C ∧ w ω C≤1) ∧
      (∀ ω C,0<w ω C → good ω ∧ C≤J ω ∧ IsEmbeddedCycle C r) ∧
      (∀ ω u v,(∑ C,if C.Adj u v then w ω C else 0)=
        if good ω ∧ (J ω).Adj u v then 1 else 0) := by
  have hex (ω : Ω) : ∃ w : SimpleGraph V → ℝ,
      (∀ C,0≤w C ∧ w C≤1) ∧
      (∀ C,0<w C → good ω ∧ C≤J ω ∧ IsEmbeddedCycle C r) ∧
      (∀ u v,(∑ C,if C.Adj u v then w C else 0)=
        if good ω ∧ (J ω).Adj u v then 1 else 0) := by
    by_cases hg : good ω
    · obtain ⟨w,hw,hs,he⟩ := hf ω hg
      exact ⟨w,fun C => ⟨hw C,fractional_cycle_coefficient_le_one (J ω) r w hw hs he C⟩,
        fun C hC => ⟨hg,hs C hC⟩,by simpa only [hg,true_and] using he⟩
    · refine ⟨fun _ => 0,fun _ => ⟨le_refl _,by norm_num⟩,?_,?_⟩
      · intro C hC
        exact False.elim (lt_irrefl 0 hC)
      · intro u v
        simp [hg]
  choose w hw hs he using hex
  exact ⟨w,hw,hs,he⟩

theorem fractional_cycle_sample_average {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (μ : FiniteLaw Ω) (G : SimpleGraph V) (J : Ω → SimpleGraph V) (r : ℕ)
    (good : Ω → Prop) (hsub : ∀ ω,J ω≤G)
    (hf : ∀ ω,good ω → HasFractionalDecomposition (J ω) (fun C => IsEmbeddedCycle C r))
    (t : ℝ) (ht : 0<t) :
    ∃ a : SimpleGraph V → ℝ,
      (∀ C,0≤a C) ∧
      (∀ C,0<a C → C≤G ∧ IsEmbeddedCycle C r) ∧
      (∀ C,a C≤μ.probability (fun ω => good ω ∧ C≤J ω)/t) ∧
      (∀ u v,(∑ C,if C.Adj u v then a C else 0)=
        μ.probability (fun ω => good ω ∧ (J ω).Adj u v)/t) ∧
      (∀ u v,μ.probability (fun ω => (J ω).Adj u v)/t-
          (∑ C,if C.Adj u v then a C else 0)=
        μ.probability (fun ω => ¬good ω ∧ (J ω).Adj u v)/t) := by
  obtain ⟨w,hw,hs,he⟩ := fractional_cycle_sample_weights J r good hf
  let a (C : SimpleGraph V) := (∑ ω,μ.mass ω*w ω C)/t
  have ha (C : SimpleGraph V) : 0≤a C := by
    exact div_nonneg (Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hw ω C).1)) ht.le
  have hload (u v : V) : (∑ C,if C.Adj u v then a C else 0)=
      μ.probability (fun ω => good ω ∧ (J ω).Adj u v)/t := by
    calc
      _ = (∑ C,∑ ω,μ.mass ω*(if C.Adj u v then w ω C else 0))/t := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro C _
        by_cases hC : C.Adj u v <;> simp [a,hC]
      _ = (∑ ω,μ.mass ω*(∑ C,if C.Adj u v then w ω C else 0))/t := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = _ := by
        simp only [he,FiniteLaw.probability,mul_ite,mul_one,mul_zero]
        congr 1
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> rfl
  refine ⟨a,ha,?_,?_,hload,?_⟩
  · intro C hC
    have hp : 0<∑ ω,μ.mass ω*w ω C := (div_pos_iff_of_pos_right ht).mp hC
    obtain ⟨ω,_,hω⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun ω _ => mul_nonneg (μ.nonneg ω) (hw ω C).1)).mp hp
    have hwpos : 0<w ω C := (mul_pos_iff.mp hω).elim And.right
      (fun hh => False.elim (not_lt_of_ge (μ.nonneg ω) hh.1))
    exact ⟨(hs ω C hwpos).2.1.trans (hsub ω),(hs ω C hwpos).2.2⟩
  · intro C
    apply div_le_div_of_nonneg_right _ ht.le
    unfold FiniteLaw.probability
    apply Finset.sum_le_sum
    intro ω _
    by_cases hgood : good ω ∧ C≤J ω
    · simp only [if_pos hgood]
      exact (mul_le_mul_of_nonneg_left (hw ω C).2 (μ.nonneg ω)).trans_eq (mul_one _)
    · have hz : w ω C=0 := by
        by_contra hn
        have hp : 0<w ω C := lt_of_le_of_ne (hw ω C).1 (Ne.symm hn)
        exact hgood ⟨(hs ω C hp).1,(hs ω C hp).2.1⟩
      simp [hz,hgood]
  · intro u v
    rw [hload,← sub_div]
    congr 1
    unfold FiniteLaw.probability
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hg : good ω <;> by_cases hj : (J ω).Adj u v <;> simp [hg,hj]

end Oberwolfach
