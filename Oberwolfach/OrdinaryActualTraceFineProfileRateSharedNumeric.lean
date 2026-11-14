module

public import Oberwolfach.OrdinaryActualTraceBalanceAndFineCoverAt
public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceOrdered
public import Oberwolfach.OrdinaryVortexDeepTraceFineNumericSharedBeforeBeta
public import Oberwolfach.OrdinaryVortexBufferedTraceSeparatedLinearCostAndRate
public import Oberwolfach.OrdinaryDeepTraceCoverAndBalanceOrdered

@[expose] public section
/-! Boundary rates are fixed linearly in the vortex scale before the cover's
later balance tolerance and the current trace are selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_trace_fine_profile_rate_shared_numeric
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer)
    (ρ₀ hmin href δlimit a ρ θ α pmin ηProfile:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hα:0<α) (hpmin:0<pmin) (hηProfile:0<ηProfile):
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀rateParent:ℝ,0<rateParent→
    ∃ζ δ rate:ℝ,0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ 0<δ ∧ δ≤α ∧ 0<rate ∧
    ∀aLoad:ℝ,0<aLoad→aLoad≤1→
    ∃ξ η₀:ℝ,ξ=min (ε/200) (aLoad^2/160) ∧ η₀=δcut*(ρ₀/8)*ξ/1000 ∧ 0<ξ ∧ 0<η₀ ∧ ∀η:ℝ,0<η→η≤η₀→
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃mBalance mCover:ℕ,1≤mBalance ∧ 1≤mCover ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d buffer β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalance mWheel K buffer ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hNumeric,hcover⟩:=
    ordinary_vortex_actual_trace_fine_numeric_shared_before_beta mWheel K buffer hm hbuffer ρ₀ hmin href δlimit a ρ θ
      hρ₀ hhmin hhref hδlimit ha hρ hθ
  obtain ⟨cBoundary,hcBoundary,hbalance⟩:=ordinary_vortex_actual_trace_separated_cost_and_rate
    ρ₀ α pmin hmin d buffer hbuffer hρ₀ hα hpmin hhmin
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,?_⟩
  intro ε hε hεvortex rateParent hrate
  let ζ:ℝ:=min ζlimit rateParent
  have hζ:0<ζ:=lt_min hζlimit hrate
  obtain ⟨δ,rate,hδ,hδα,hrateC,hbalance⟩:=hbalance ε hε (lt_of_le_of_lt hεvortex hεvortex1) ηProfile ζ hηProfile hζ
  refine ⟨ζ,δ,rate,hζ,min_le_left _ _,min_le_right _ _,hδ,hδα,hrateC,?_⟩
  intro aLoad haLoad haLoad1
  obtain ⟨ξ,η₀,hξEq,hηEq,hξ,hη₀,hcover⟩:=hcover ε hε hεvortex aLoad haLoad haLoad1
  refine ⟨ξ,η₀,hξEq,hηEq,hξ,hη₀,?_⟩
  intro η hη hη0 β hβ hβ1 hβδ C hC
  obtain ⟨mb,hmb,hbalance⟩:=hbalance β hβ hβ1 hβδ C hC
  obtain ⟨mc,hmc,hcover⟩:=hcover β hβ hβ1 d
  exact ⟨mb,mc,hmb,hmc,hbalance,hcover η hη.le hη0⟩
end Oberwolfach
