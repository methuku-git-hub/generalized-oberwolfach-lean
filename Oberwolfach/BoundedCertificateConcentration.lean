module

public import Oberwolfach.CertificateConcentration

@[expose] public section

/-! A mean-centred concentration bound for bounded variables with
coordinate certificates. The finite truncation condition is explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_bounded_certificate_tail
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (R : (I → Ω) → ℝ)
    {c D M t : ℝ} (hc : 0<c) (hD : 0<D) (ht : 0≤t)
    (hcert : HasCoordinateCertificateBound R c D)
    (hrange : ∀ x,0≤R x ∧ R x≤M)
    (hsmall : M*(4*Real.exp (-t^2/(4*c*D)))≤t) :
    (FiniteLaw.pi μ).probability
      (fun x=>3*t≤|R x-(FiniteLaw.pi μ).expectation R|)≤
        4*Real.exp (-t^2/(4*c*D)) := by
  classical
  let ν := FiniteLaw.pi μ
  obtain ⟨z,hlo,hhi⟩ := finiteLaw_exists_median ν R
  let m := R z
  have hM0 : 0≤M := (hrange z).1.trans (hrange z).2
  have hbound (x : I → Ω) : |R x-m|≤M := by
    apply abs_le.mpr
    constructor <;> dsimp [m] <;> linarith [(hrange x).1,(hrange x).2,(hrange z).1,(hrange z).2]
  have hmed := finiteLaw_certificate_median_tail μ R hc hD ht hcert hlo hhi
  have hm : |ν.expectation R-m|≤2*t := by
    have he : ν.expectation (fun x=>R x-m)=ν.expectation R-m := by
      unfold FiniteLaw.expectation
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,ν.total,one_mul]
    have ha := finiteLaw_abs_expectation_le ν (fun x=>R x-m)
    rw [he] at ha
    have hb := finiteLaw_expectation_abs_truncate ν (fun x=>R x-m) ht hbound
    have hp := mul_le_mul_of_nonneg_left hmed hM0
    linarith
  have hsubset (x : I → Ω) (hx : 3*t≤|R x-ν.expectation R|) :
      t≤|R x-m| := by
    have htri := abs_sub_le (R x) m (ν.expectation R)
    rw [abs_sub_comm m (ν.expectation R)] at htri
    linarith
  exact (finiteLaw_probability_mono ν _ _ hsubset).trans hmed

end Oberwolfach
