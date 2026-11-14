module

public import Oberwolfach.OrdinaryTriangleEarlyBalanceSelectors
public import Oberwolfach.OrdinaryTriangleParentRateAndSampleTolerance

@[expose] public section
/-! Fix the parent rate and common sample tolerance first, then obtain the
initial and later protected-balance rates before choosing spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_tolerance_and_deep_balance
    (ρ₀ α pmin hmin cBoundary ηProfile:ℝ)
    (hDeep:OrdinaryTriangleInitialDeepBalanceSelector ρ₀ α pmin hmin cBoundary) (hηProfile:0<ηProfile)
    (βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε:ℝ) (N₀:ℕ)
    (hN₀:1≤N₀) (hroot:0<rateRoot) (hlam:0<lamInner) (hδ:0<δend) (hε:0<ε) (hεsmall:ε<1/4)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateRoot N₀)
    (capHub ζlimit:ℝ) (hHub:0<capHub) (hLimit:0<ζlimit):
    ∃rateParent ζcert δDeep rate:ℝ,
      0<rateParent ∧ rateParent≤rateRoot ∧ rateParent≤lamInner*ε/4 ∧ rateParent≤δend*ε/8 ∧
      OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζparent rateParent N₀ ∧
      0<ζcert ∧ ζcert≤rateParent ∧ ζcert≤capHub ∧ ζcert≤ζlimit ∧
      0<δDeep ∧ δDeep≤α ∧ 0<rate ∧
    ∀ηInitial:ℝ,0<ηInitial→∃δInitial:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance:ℕ,1≤mInitial ∧ 1≤mBalance ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζcert cBoundary δDeep rate d 2 β C mBalance :=by
  obtain ⟨rateParent,ζcert,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζhub,hζlimit⟩:=
    ordinary_triangle_parent_rate_and_sample_tolerance βH ηH B ω pstar βparent εparent ζparent rateRoot lamInner δend ε N₀
      hN₀ hroot hlam hδ hε hscale capHub ζlimit hHub hLimit
  obtain ⟨δDeep,rate,hδDeep,hδα,hrateDeep,hcallbacks⟩:=hDeep ε hε hεsmall ηProfile ζcert hηProfile hζ
  exact ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',
    hζ,hζrate,hζhub,hζlimit,hδDeep,hδα,hrateDeep,hcallbacks⟩
end Oberwolfach
