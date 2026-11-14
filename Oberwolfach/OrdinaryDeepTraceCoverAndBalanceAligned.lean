module

public import Oberwolfach.OrdinaryDeepTraceCoverAndBalanceOrdered

@[expose] public section
/-! Choose one positive edit cap below both the cover and parent-reference
budgets before the vortex error and finite host are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_trace_cover_and_balance_aligned
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer)
    (ρ₀ hmin href δlimit a ρ θ:ℝ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀aLoad:ℝ,0<aLoad→aLoad≤1→
    ∃ξ η₀:ℝ,0<ξ ∧ 0<η₀ ∧ ∀η:ℝ,0<η→η≤η₀→
    ∀(α pmin rateParent:ℝ),0<α→0<pmin→0<rateParent→∀d:ℕ,
    ∃ζ δ rate:ℝ,0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ 0<δ ∧ δ≤α ∧ 0<rate ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃mBalance mCover:ℕ,1≤mBalance ∧ 1≤mCover ∧
      OrdinaryDeepTraceBalanceAt ε ρ₀ α pmin hmin η ζ δ rate d buffer β C mBalance ∧
      OrdinaryDeepTraceCoverAt mWheel K buffer ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hmain⟩:=
    ordinary_deep_trace_cover_and_balance_ordered mWheel K buffer hm hbuffer ρ₀ hmin href δlimit a ρ θ
      hρ₀ hhmin hhref hδlimit ha hρ hθ
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,?_⟩
  intro ε hε hεvortex aLoad haLoad haLoad1
  obtain ⟨ξ,η₀,hξ,hη₀,hmain⟩:=hmain ε hε hεvortex aLoad haLoad haLoad1
  refine ⟨ξ,η₀,hξ,hη₀,?_⟩
  intro η hη hη0 α pmin rateParent hα hpmin hrate d
  let ζ:ℝ:=min ζlimit rateParent
  have hζ:0<ζ:=lt_min hζlimit hrate
  obtain ⟨δ,rate,hδ,hδα,hrateC,hmain⟩:=hmain η hη hη0 α pmin ζ hα hpmin hζ d
  exact ⟨ζ,δ,rate,hζ,min_le_left _ _,min_le_right _ _,hδ,hδα,hrateC,hmain⟩
end Oberwolfach
