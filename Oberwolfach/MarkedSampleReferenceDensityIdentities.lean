module

public import Oberwolfach.MarkedSeedDensities

@[expose] public section
/-! The common-event weight normalization and the reference step use the
same density lower bound, not merely comparable bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_sample_reference_density_identities
    (m:ℕ) (hm:0<m) (ρ s ρ₀ sstar:ℝ):
    let t₀:=sstar/m
    let t:=s/m
    let p0:=ρ₀*sstar/(2*m)
    let p:=ρ*s/2
    let k:=p/m;
    p0=ρ₀*t₀/2 ∧ p=ρ*m*t/2 ∧ k=ρ*t/2 ∧ p0/2=ρ₀*t₀/4:=by
  intro t₀ t p0 p k
  have hm0:(m:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hm)
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [t₀,t,p0,p,k] <;> field_simp [hm0] <;> ring
end Oberwolfach
