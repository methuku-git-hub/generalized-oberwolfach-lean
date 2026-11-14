module

public import Oberwolfach.MarkedReferenceCenterIdentities

@[expose] public section
/-! The original marked-wheel density definitions give the common balance
centers, with the same number of hubs and no new parameter assumption. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_reference_density_centers (rho t U:ℝ) (r:ℕ) (hρ:rho≠0):
    let m:ℝ:=(r+4:ℕ)
    let p:=rho*m*t/2
    let k:=p/m;
    p*(2*U/rho)=m*(t*U) ∧ k*(2*U/rho)=t*U:=by
  intro m p k
  have hm:m≠0:=by dsimp [m];positivity
  dsimp [p,k]
  constructor <;> field_simp <;> ring
end Oberwolfach
