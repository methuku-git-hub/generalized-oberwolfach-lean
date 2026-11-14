module

public import Oberwolfach.MarkedFixedVortexInnerDegrees

@[expose] public section
/-! Exact density-centre identities for the original marked sampling law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_density_centre_identities
    (ρ s b h:ℝ) (m:ℕ) (hρ:0<ρ) (hm:0<m):
    let p:=ρ*s/2
    let k:=p/(m:ℝ)
    let Dbal:=2*b/ρ
    let Dload:=2*h/ρ
    p*Dbal=s*b ∧ k*Dbal=(s/m)*b ∧
    h*(s/m)=Dload*k ∧ h*(s/m)*m=Dload*p:=by
  intro p k Dbal Dload
  have hρ0:ρ≠0:=ne_of_gt hρ
  have hm0:(m:ℝ)≠0:=ne_of_gt (by exact_mod_cast hm)
  dsimp [p,k,Dbal,Dload]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp
end Oberwolfach
