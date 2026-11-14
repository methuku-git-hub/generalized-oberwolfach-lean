module

public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData

@[expose] public section
/-! Choose the positive common reference marginal before the host and sample;
the original assigned law supplies both the rim and spoke lower bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_vortex_marginal_floor
    (ρ₀ smin:ℝ) (hρ₀:0<ρ₀) (hsmin:0<smin):
    ∃pmin:ℝ,0<pmin ∧ pmin≤1 ∧ pmin≤ρ₀*smin ∧
    ∀{n D K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
      (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (i₀:Fin K) (rsv θ c:ℝ) (d:ℕ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d),
      pmin≤2*(initialIndexDensity U D*rsv/2) ∧ pmin≤rsv ∧ rsv≤1 ∧
      2*(initialIndexDensity U D*rsv/2)=initialIndexDensity U D*rsv ∧
      (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) :=by
  let pmin:=min (1:ℝ) (ρ₀*smin)
  have hp:0<pmin:=by dsimp [pmin];positivity
  have hp1:pmin≤1:=min_le_left _ _
  have hpp:pmin≤ρ₀*smin:=min_le_right _ _
  refine ⟨pmin,hp,hp1,hpp,?_⟩
  intro n D K U _ _ F hF i₀ rsv θ c d sampling
  refine ⟨hpp.trans sampling.hpmin,hpp.trans sampling.hsmin,sampling.hrsv,?_,sampling.hfalse⟩
  ring
end Oberwolfach
