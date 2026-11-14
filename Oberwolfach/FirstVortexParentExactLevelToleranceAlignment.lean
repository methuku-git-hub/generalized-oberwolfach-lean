module

public import Oberwolfach.FirstVortexParentCoefficientAlignment

@[expose] public section
/-! Use the level theorem's actual tolerance, without changing the level
parameters, for the same parent event and selector. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_exact_level_tolerance_alignment
    (r:ℕ) (ρ₀ sstar tstar B δ κ thetaDeep eta ε:ℝ)
    (hρ₀:0<ρ₀) (hs:0<sstar) (ht:0<tstar)
    (htsmall:tstar≤sstar/(((r+4):ℕ):ℝ)) (hB:0≤B) (hδ:0≤δ) (hε:0<ε):
    let m:ℝ:=((r+4):ℕ)
    let pLevel:=ρ₀*tstar/2
    let pSelector:=ρ₀*sstar/(2*m)
    let CpLevel:=11*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let CpSelector:=11*(m+1)^4*(2*B/pSelector^(2*(r+4)+1))
    let ClLevel:=5*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let ClSelector:=5*(m+1)^4*(2*B/pSelector^(2*(r+4)+1));
    δ+δ+CpLevel*δ≤κ/4→δ+δ+CpLevel*δ≤thetaDeep/4→
    δ+δ+ClLevel*(4/ε)*δ≤eta/4→δ+δ≤tstar/8→
    δ+δ+CpSelector*δ≤κ/4 ∧ δ+δ+CpSelector*δ≤thetaDeep/4 ∧
    δ+δ+ClSelector*(4/ε)*δ≤eta/4 ∧ δ+δ≤(sstar/m)/8 :=by
  intro m pLevel pSelector CpLevel CpSelector ClLevel ClSelector hParent hDeep hLoad hRow
  obtain ⟨_,_,hCp,_,hCl⟩:=first_vortex_parent_coefficient_alignment r ρ₀ sstar tstar B δ ε hρ₀ hs ht htsmall hB hδ hε
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [hParent,hCp]
  · linarith only [hDeep,hCp]
  · linarith only [hLoad,hCl]
  · linarith only [hRow,htsmall]
end Oberwolfach
