module

public import Oberwolfach.LongActualOrdinaryDensityLower
public import Oberwolfach.LongAllHubSeedCoefficients

@[expose] public section
/-! The actual seed coefficients are uniformly bounded without assuming
that a coefficient is at most one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_seed_coefficient_le_four
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (hθ0:0≤θ) (hθ1:θ≤1)
    (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u):
    ∀i:Fin K,∀u,
      0≤longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u ∧
      longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u≤4:=by
  have hbpos:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u:=by
    intro u
    have h:=hb u
    linarith
  intro i u
  have h:=long_assigned_all_ordinary_seed_coefficients hn F hF K m θ hθ0 hθ1 hbpos i u
  refine ⟨h.1,h.2.trans ?_⟩
  apply (div_le_iff₀ (hbpos u)).2
  have hh:=hb u
  linarith
end Oberwolfach
