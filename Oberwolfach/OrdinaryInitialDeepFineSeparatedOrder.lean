module

public import Oberwolfach.OrdinaryDeepTraceFineGeometryAlignedOrder
public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt
public import Oberwolfach.OrdinaryDeepTraceSeparatedBalanceBoundaryMonotone

@[expose] public section
/-! Select the deep profile rate before the fine load and initial-balance
tolerance. Both balance callbacks then use one earlier boundary coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_deep_fine_separated_order
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer)
    (ρ₀ hmin href δlimit a ρ θ α pmin ηProfile:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hα:0<α) (hpmin:0<pmin) (hηProfile:0<ηProfile):
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀rateParent:ℝ,0<rateParent→
    ∃ζ δDeep rate:ℝ,0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ 0<δDeep ∧ δDeep≤α ∧ 0<rate ∧
    ∀ηinitial aLoad ξroot η₀ ηbal:ℝ,0<ηinitial→0<aLoad→aLoad≤1→
      ξroot=min (ε/200) (aLoad^2/160)→η₀=δcut*(ρ₀/8)*ξroot/1000→0<ηbal→ηbal≤η₀→
    ∃δInitial:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηinitial ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance mCover:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧
      OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηinitial cBoundary δInitial d β mInitial ∧
      OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d buffer β C mBalance ∧
      OrdinaryDeepTraceFineCoverAtLocalBalance mWheel K buffer ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover:=by
  obtain ⟨cI,hcI,hInitial⟩:=ordinary_vortex_initial_ambient_balance_at_choice ρ₀ α pmin hmin d hρ₀ hα hpmin hhmin
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cD,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,
    hεsample,hεvortex,hεvortex1,hcD,hDeep⟩:=
    ordinary_deep_trace_fine_geometry_aligned_order mWheel K buffer hm hbuffer
      ρ₀ hmin href δlimit a ρ θ α pmin ηProfile d hρ₀ hhmin hhref hδlimit ha hρ hθ hα hpmin hηProfile
  let cBoundary:=min cI cD
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,
    hεsample,hεvortex,hεvortex1,lt_min hcI hcD,?_⟩
  intro ε hε hεvortex rateParent hrateParent
  obtain ⟨ζ,δDeep,rate,hζ,hζlimit',hζrate,hδDeep,hδα,hrate,hDeep⟩:=hDeep ε hε hεvortex rateParent hrateParent
  refine ⟨ζ,δDeep,rate,hζ,hζlimit',hζrate,hδDeep,hδα,hrate,?_⟩
  intro ηinitial aLoad ξroot η₀ ηbal hηinitial haLoad haLoad1 hξroot hη₀ hηbal hηbal0
  obtain ⟨δInitial,hδInitial,hδIα,hδIη,hInitial⟩:=hInitial ε hε (lt_of_le_of_lt hεvortex hεvortex1) ηinitial hηinitial
  refine ⟨δInitial,hδInitial,hδIα,hδIη,?_⟩
  intro β hβ hβ1 hβI hβD C hC
  obtain ⟨mInitial,hmInitial,hI⟩:=hInitial β hβ hβ1 hβI
  obtain ⟨mBalance,mCover,hmBalance,hmCover,hD,hCover⟩:=
    hDeep aLoad ξroot η₀ ηbal haLoad haLoad1 hξroot hη₀ hηbal hηbal0 β hβ hβ1 hβD C hC
  refine ⟨mInitial,mBalance,mCover,hmInitial,hmBalance,hmCover,?_,?_,hCover⟩
  · exact ordinary_vortex_initial_ambient_balance_at_monotone ε ρ₀ α pmin hmin ηinitial
      cBoundary cI δInitial δInitial d β mInitial mInitial hε.le (min_le_left _ _) le_rfl le_rfl hI
  · exact ordinary_deep_trace_separated_balance_boundary_monotone ε ρ₀ α pmin hmin ηProfile ζ
      cBoundary cD δDeep rate d buffer β C mBalance mBalance hε.le (min_le_right _ _) le_rfl hD
end Oberwolfach
