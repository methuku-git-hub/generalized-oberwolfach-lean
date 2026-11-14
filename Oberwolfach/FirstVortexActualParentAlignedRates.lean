module

public import Oberwolfach.FirstVortexActualParentToleranceAlignment

@[expose] public section
/-! The actual selector-coefficient parent and balance tolerances, as a
reusable proposition after the level inequalities have been discharged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def FirstVortexActualParentAlignedRates
    (r:ℕ) (ρ₀ sstar tstar B δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff:ℝ):Prop :=
    let m:ℝ:=((r+4):ℕ)
    let pLevel:=ρ₀*tstar/2
    let pSelector:=ρ₀*sstar/(2*m)
    let CpLevel:=11*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let CpSelector:=11*(m+1)^4*(2*B/pSelector^(2*(r+4)+1))
    let ClLevel:=5*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let ClSelector:=5*(m+1)^4*(2*B/pSelector^(2*(r+4)+1));
    ∃δ' εBal ζBal:ℝ,0<δ' ∧ δ'≤δ ∧ 2*δ'≤ζCfg ∧
      δ'≤(κ/2)/4 ∧ δ'+((r+12:ℕ):ℝ)*δ'≤(κ/2)/4 ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤(x/2)/2 ∧
      δ'+δ'+CpSelector*δ'≤(κ/2)/4 ∧ δ'+δ'+CpSelector*δ'≤(thetaDeep/2)/4 ∧
      δ'+δ'+ClSelector*(4/ε)*δ'≤(eta/2)/4 ∧
      δ'+δ'≤tstar/16 ∧ δ'+δ'≤(sstar/m)/8 ∧
      0<εBal ∧ 0<ζBal ∧ εBal≤cap₁ ∧ ζBal≤cap₂ ∧
      εBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧ εBal+((r+4)+2:ℕ)*ζBal≤x/4 ∧
      3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*δ' ∧
      3*βA≤pathCoeff-((r+4:ℕ):ℝ)*δ'
end Oberwolfach
