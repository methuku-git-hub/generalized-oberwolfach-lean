module

public import Oberwolfach.CertificateConcentration

@[expose] public section

/-! Counting events witnessed by small sets of coordinates. A coordinate
is charged once for each witnessed event containing it, with multiplicity
retained in the certificate weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteWitness_coordinate_certificate_on
    {I J Ω : Type*} [Fintype I]
    (T : Finset J) (P : J → (I → Ω) → Prop) (S : (I → Ω) → J → Finset I)
    {k : ℕ} {c M : ℝ} (hM : ∀ x,((T.filter (fun j=>P j x)).card : ℝ)≤M)
    (hsize : ∀ x j,j∈T → P j x → (S x j).card≤k)
    (hload : ∀ x i,((T.filter (fun j=>P j x ∧ i∈S x j)).card : ℝ)≤c)
    (hwitness : ∀ x j,j∈T → P j x → ∀ y,(∀ i∈S x j,x i=y i) → P j y) :
    HasCoordinateCertificateBound
      (fun x=>((T.filter (fun j=>P j x)).card : ℝ)) c ((k : ℝ)*M) := by
  classical
  intro x
  let A := T.filter (fun j=>P j x)
  let w : I → ℝ := fun i=>∑ j∈A,if i∈S x j then (1 : ℝ) else 0
  have hw0 (i : I) : 0≤w i := Finset.sum_nonneg (fun j _=>by split_ifs <;> norm_num)
  have hwle (i : I) : w i≤c := by
    have he : w i=((T.filter (fun j=>P j x ∧ i∈S x j)).card : ℝ) := by
      unfold w A
      rw [Finset.sum_filter]
      simp only [← ite_and]
      rw [Finset.sum_boole]
    rw [he]
    exact hload x i
  refine ⟨w,fun i=>⟨hw0 i,hwle i⟩,?_,?_⟩
  · have he : (∑ i,w i)=∑ j∈A,((S x j).card : ℝ) := by
      unfold w
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_ite_mem]
      simp
    rw [he]
    calc
      _ ≤ ∑ _j∈A,(k : ℝ) := Finset.sum_le_sum (fun j hj=>by
        exact_mod_cast hsize x j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2)
      _ = (k : ℝ)*(A.card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hM x) (Nat.cast_nonneg _)
  · intro y
    let a : J → I → ℝ := fun j i=>if x i≠y i ∧ i∈S x j then 1 else 0
    have ha (j : J) (i : I) : 0≤a j i := by unfold a;split_ifs <;> norm_num
    have hone (j : J) (hj : j∈A) :
        (1 : ℝ)≤(if P j y then 1 else 0)+∑ i,a j i := by
      by_cases hy : P j y
      · simp only [hy,ite_true]
        have hn : 0≤∑ i,a j i := Finset.sum_nonneg (fun i _=>ha j i)
        linarith
      · have hex : ∃ i∈S x j,x i≠y i := by
          by_contra h
          push Not at h
          exact hy (hwitness x j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2 y h)
        obtain ⟨i,hi,hne⟩ := hex
        have hh := Finset.single_le_sum (s:=Finset.univ) (f:=a j)
          (fun i _=>ha j i) (Finset.mem_univ i)
        simpa [a,hne,hi,hy] using hh
    have hs := Finset.sum_le_sum hone
    rw [Finset.sum_add_distrib] at hs
    have hsurv : (∑ j∈A,if P j y then (1 : ℝ) else 0)≤
        ((T.filter (fun j=>P j y)).card : ℝ) := by
      calc
        _ ≤ ∑ j∈T,if P j y then (1 : ℝ) else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _=>by split_ifs <;> norm_num)
        _ = _ := Finset.sum_boole _ _
    have hchanges : (∑ j∈A,∑ i,a j i)=∑ i,if x i≠y i then w i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : x i=y i
      · simp [a,he]
      · simp only [a,ne_eq,he,not_false_eq_true,true_and,ite_true]
        rfl
    rw [hchanges] at hs
    have hsum : (∑ _j∈A,(1 : ℝ))=(A.card : ℝ) := by simp
    rw [hsum] at hs
    change (A.card : ℝ)≤_
    linarith

end Oberwolfach
