module

public import Oberwolfach.CertificateConcentration

@[expose] public section

/-! Pulling coordinate certificates back through a deterministic map.
Several represented coordinates may share an original random coordinate;
their certificate weights are added, not treated as independent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem coordinate_certificate_pullback
    {I K Ω C : Type*} [Fintype I] [Fintype K]
    (owner : K → I) (read : K → Ω → C) (R : (K → C) → ℝ)
    {c D : ℝ} {B : ℕ} (hc : 0≤c)
    (hB : ∀ i,(Finset.univ.filter (fun k=>owner k=i)).card≤B)
    (hcert : HasCoordinateCertificateBound R c D) :
    HasCoordinateCertificateBound
      (fun x : I → Ω=>R (fun k=>read k (x (owner k)))) (c*B) D := by
  classical
  intro x
  obtain ⟨v,hv,hs,hchange⟩ := hcert (fun k=>read k (x (owner k)))
  let w : I → ℝ := fun i=>∑ k,if owner k=i then v k else 0
  have hw0 (i : I) : 0≤w i := by
    apply Finset.sum_nonneg
    intro k _
    change 0 ≤ (if owner k=i then v k else 0)
    split_ifs
    · exact (hv k).1
    · exact le_refl _
  have hwle (i : I) : w i≤c*B := by
    have hpoint (k : K) : (if owner k=i then v k else 0)≤
        if owner k=i then c else 0 := by
      split_ifs
      · exact (hv k).2
      · exact le_refl _
    have hsum := Finset.sum_le_sum (fun k (_ : k∈Finset.univ)=>hpoint k)
    have he : (∑ k,if owner k=i then c else 0)=
        c*((Finset.univ.filter (fun k=>owner k=i)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [mul_comm]
    rw [he] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hB i) hc)
  refine ⟨w,fun i=>⟨hw0 i,hwle i⟩,?_,?_⟩
  · have he : (∑ i,w i)=∑ k,v k := by
      unfold w
      rw [Finset.sum_comm]
      simp
    rw [he]
    exact hs
  · intro y
    have hh := hchange (fun k=>read k (y (owner k)))
    have hsum : (∑ k,if read k (x (owner k))≠read k (y (owner k)) then v k else 0)≤
        ∑ k,if x (owner k)≠y (owner k) then v k else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases he : x (owner k)=y (owner k)
      · simp [he]
      · simp only [ne_eq,he,not_false_eq_true,ite_true]
        have hv0 := (hv k).1
        split_ifs <;> linarith
    have he : (∑ i,if x i≠y i then w i else 0)=
        ∑ k,if x (owner k)≠y (owner k) then v k else 0 := by
      have hpoint (i : I) :
          (if x i≠y i then w i else 0)=
            ∑ k,if owner k=i then (if x i≠y i then v k else 0) else 0 := by
        by_cases hi : x i=y i <;> simp [w,hi]
      simp_rw [hpoint]
      rw [Finset.sum_comm]
      simp
    rw [he]
    dsimp only at hh ⊢
    linarith

end Oberwolfach
