module

public import Oberwolfach.OrdinaryAssignedReferenceOriginalInputs

@[expose] public section
/-! Both initial and later certificates use these same reference means and
bounds, derived from the actual assigned sampling law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_wheel_sample_inputs
    {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    let pstar:=ρ₀*smin/2
    let pR:=2*(initialIndexDensity U D*rsv/2);
    0<pstar ∧ pstar≤pR ∧ pR≤1 ∧ pstar≤rsv ∧ 0<rsv ∧ rsv≤1 ∧
      pR=initialIndexDensity U D*rsv ∧
      (∀u,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c u false=rsv) :=by
  intro pstar pR
  have hinputs:=ordinary_assigned_reference_original_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo sampling
  obtain ⟨_,_,_,hspoke,_,hpR,hrsv,hrsv1⟩:=hinputs
  have hprod:0<ρ₀*smin:=mul_pos hρ₀ hsmin
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  have hpR':pstar≤pR:=by dsimp [pstar,pR];linarith
  have hrsv':pstar≤rsv:=by dsimp [pstar];linarith
  have hrsv0:0<rsv:=hpstar.trans_le hrsv'
  have hρ0:0≤ initialIndexDensity U D:=hρ₀.le.trans hρlo
  have heq:pR=initialIndexDensity U D*rsv:=by dsimp [pR];ring
  have hupper:pR≤1:=by
    rw [heq]
    have hh:=mul_le_mul hρhi hrsv1 hrsv0.le (by norm_num: (0:ℝ)≤1)
    simpa using hh
  exact ⟨hpstar,hpR',hupper,hrsv',hrsv0,hrsv1,heq,hspoke⟩
end Oberwolfach
