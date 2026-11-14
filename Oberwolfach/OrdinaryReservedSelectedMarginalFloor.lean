module

public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData

@[expose] public section
/-! A positive selected-arc floor is chosen from the original density and
reserve floors, before the cutoff and matching error. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_selected_marginal_floor
    (ρ₀ smin:ℝ) (hρ₀:0<ρ₀) (hsmin:0<smin):
    ∃pstar:ℝ, pstar=(min 1 (ρ₀*smin))/2 ∧ 0<pstar ∧ pstar≤1 ∧
    ∀{n D K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
      (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (i₀:Fin K) (rsv θ c:ℝ) (d:ℕ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d),
      pstar≤ initialIndexDensity U D*rsv/2 ∧
      (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) :=by
  let pstar:ℝ:=(min 1 (ρ₀*smin))/2
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hp1:2*pstar≤1:=by dsimp [pstar];linarith [min_le_left (1:ℝ) (ρ₀*smin)]
  have hpρ:2*pstar≤ρ₀*smin:=by dsimp [pstar];linarith [min_le_right (1:ℝ) (ρ₀*smin)]
  refine ⟨pstar,rfl,hp,by linarith,?_⟩
  intro n D K U _ _ F hF i₀ rsv θ c d sampling
  constructor
  · linarith [sampling.hpmin]
  · exact sampling.hfalse
end Oberwolfach
