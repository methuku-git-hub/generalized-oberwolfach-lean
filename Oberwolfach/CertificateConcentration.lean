module

public import Oberwolfach.FiniteTalagrand
public import Oberwolfach.ConvexDistanceCertificates
public import Oberwolfach.FiniteMedian

@[expose] public section

/-! Concentration from bounded coordinate certificates. The certificates
may depend on the realised configuration; the probability law is fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def HasCoordinateCertificateBound {I Ω : Type*} [Fintype I]
    (R : (I → Ω) → ℝ) (c D : ℝ) : Prop :=
  ∀ x,∃ w : I → ℝ,(∀ i,0≤w i ∧ w i≤c) ∧ (∑ i,w i)≤D ∧
    ∀ y,R x≤R y+∑ i,if x i≠y i then w i else 0

theorem finiteLaw_probability_or_le
    {Γ : Type*} [Fintype Γ] (ν : FiniteLaw Γ) (A B : Γ → Prop) :
    ν.probability (fun x=>A x ∨ B x)≤ν.probability A+ν.probability B := by
  classical
  unfold FiniteLaw.probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hA : A x <;> by_cases hB : B x <;> simp [hA,hB,ν.nonneg x]

theorem finiteLaw_certificate_separated_tails
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (R : (I → Ω) → ℝ)
    {c D t m : ℝ} (hc : 0<c) (hD : 0<D) (ht : 0≤t)
    (hcert : HasCoordinateCertificateBound R c D) :
    (FiniteLaw.pi μ).probability (fun x=>R x≤m)*
      (FiniteLaw.pi μ).probability (fun x=>m+t≤R x)≤
      Real.exp (-t^2/(4*c*D)) := by
  classical
  let ν := FiniteLaw.pi μ
  let A := Finset.univ.filter (fun x=>R x≤m)
  have hmem (x : I → Ω) : x∈A ↔ R x≤m := by simp [A]
  have hp : ν.probability (fun x=>x∈A)=ν.probability (fun x=>R x≤m) :=
    finiteLaw_probability_congr ν _ _ hmem
  have hp0 := finiteLaw_probability_nonneg ν (fun x=>R x≤m)
  by_cases hpos : 0<ν.probability (fun x=>R x≤m)
  · have hAne := finiteLaw_positive_finset_nonempty ν A (hp.symm ▸ hpos)
    have hcost (x : I → Ω) (hx : m+t≤R x) :
        t^2/(c*D)≤convexDistanceSq A x := by
      obtain ⟨w,hw,hs,hchange⟩ := hcert x
      have hh := convexDistanceSq_value_certificate R A hAne x w hc.le ht hw hs
        (fun y hy=>(hmem y).mp hy) hx hchange
      apply (div_le_iff₀ (mul_pos hc hD)).mpr
      nlinarith
    have hmono := finiteLaw_probability_mono ν (fun x=>m+t≤R x)
      (fun x=>t^2/(c*D)≤convexDistanceSq A x) hcost
    have htail := finiteLaw_convexDistance_tail μ A (t^2/(c*D))
    change ν.probability (fun x=>x∈A)*_≤_ at htail
    rw [hp] at htail
    have he : -(t^2/(c*D))/4=-t^2/(4*c*D) := by ring
    rw [he] at htail
    exact (mul_le_mul_of_nonneg_left hmono hp0).trans htail
  · have hz : ν.probability (fun x=>R x≤m)=0 := le_antisymm (le_of_not_gt hpos) hp0
    change ν.probability (fun x=>R x≤m)*_≤_
    rw [hz,zero_mul]
    exact (Real.exp_pos _).le

theorem finiteLaw_certificate_median_tail
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (R : (I → Ω) → ℝ)
    {c D t m : ℝ} (hc : 0<c) (hD : 0<D) (ht : 0≤t)
    (hcert : HasCoordinateCertificateBound R c D)
    (hlo : 1/2≤(FiniteLaw.pi μ).probability (fun x=>R x≤m))
    (hhi : 1/2≤(FiniteLaw.pi μ).probability (fun x=>m≤R x)) :
    (FiniteLaw.pi μ).probability (fun x=>t≤|R x-m|)≤
      4*Real.exp (-t^2/(4*c*D)) := by
  classical
  let ν := FiniteLaw.pi μ
  have hu := finiteLaw_certificate_separated_tails μ R hc hD ht hcert (m:=m)
  have hl := finiteLaw_certificate_separated_tails μ R hc hD ht hcert (m:=m-t)
  have he : m-t+t=m := by ring
  rw [he] at hl
  have hu' : ν.probability (fun x=>m+t≤R x)≤2*Real.exp (-t^2/(4*c*D)) := by
    have hh := mul_le_mul_of_nonneg_right hlo
      (finiteLaw_probability_nonneg ν (fun x=>m+t≤R x))
    nlinarith
  have hl' : ν.probability (fun x=>R x≤m-t)≤2*Real.exp (-t^2/(4*c*D)) := by
    have hh := mul_le_mul_of_nonneg_left hhi
      (finiteLaw_probability_nonneg ν (fun x=>R x≤m-t))
    nlinarith
  have hm := finiteLaw_probability_mono ν (fun x=>t≤|R x-m|)
    (fun x=>R x≤m-t ∨ m+t≤R x) (by
      intro x hx
      obtain h|h := le_abs.mp hx
      · right;linarith
      · left;linarith)
  have ho := finiteLaw_probability_or_le ν (fun x=>R x≤m-t) (fun x=>m+t≤R x)
  linarith

end Oberwolfach
