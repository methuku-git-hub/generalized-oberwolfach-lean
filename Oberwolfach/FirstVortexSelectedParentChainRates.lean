module

public import Oberwolfach.FirstVortexActualParentAlignedAt

@[expose] public section
/-! Extract the selected parent tolerances in the form required by the
first-vortex level-chain continuation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selected_parent_chain_rates
    (r:ℕ) (ρ₀ sstar tstar B δbase ζFixed κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ εBal ζBal:ℝ)
    (hAt:FirstVortexActualParentAlignedAt r ρ₀ sstar tstar B δbase ζFixed κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff δ εBal ζBal):
    let m:ℝ:=(r+4:ℕ)
    let pSelector:=ρ₀*sstar/(2*m)
    let Cparent:=11*(m+1)^4*(2*B/pSelector^(2*(r+4)+1))
    let Clocal:=5*(m+1)^4*(2*B/pSelector^(2*(r+4)+1));
    0≤δ ∧ 0≤εBal ∧ 0≤ζBal ∧ 2*δ≤ζFixed ∧
    δ≤(κ/2)/4 ∧ δ+(r+12:ℕ)*δ≤(κ/2)/4 ∧ δ+(r+12:ℕ)*δ≤(x/2)/2 ∧
    δ+δ+Cparent*δ≤(κ/2)/4 ∧ δ+δ+Cparent*δ≤(thetaDeep/2)/4 ∧
    δ+δ+Clocal*(4/ε)*δ≤(eta/2)/4 ∧ δ+δ+Clocal*(4/ε)*δ≤eta/8 ∧
    δ+δ≤tstar/16 ∧ δ+δ≤(sstar/m)/8 ∧
    εBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧ εBal+((r+4)+2:ℕ)*ζBal≤(x/2)/2 ∧
    3*βA≤cycleCoeff-(r+5:ℕ)*δ ∧ 3*βA≤pathCoeff-(r+4:ℕ)*δ :=by
  intro m pSelector Cparent Clocal
  dsimp [FirstVortexActualParentAlignedAt] at hAt
  obtain ⟨hδ,hδbase,hcfg,hδκ,hRefκ,hRefx,hParκ,hParDeep,hLoad,hRowT,hRowS,hε,hζ,hεcap,hζcap,hBal,hMargin,hCycle,hPath⟩:=hAt
  refine ⟨hδ.le,hε.le,hζ.le,hcfg,hδκ,hRefκ,hRefx,hParκ,hParDeep,hLoad,?_,hRowT,hRowS,hBal,?_,hCycle,hPath⟩ <;> linarith
end Oberwolfach
