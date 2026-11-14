module

public import Oberwolfach.OrdinaryActualTraceFineProfileRateSharedNumericLocalHost

@[expose] public section
/-! The profile rate can be chosen before the fresh sample and before the
fine cover load. The later geometry can supply its own smaller balance
tolerance, with exactly the same fine-cover parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_trace_fine_geometry_shared_numeric_local_host
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
    ∀aLoad ξroot η₀ ηbal:ℝ,0<aLoad→aLoad≤1→
      ξroot=min (ε/200) (aLoad^2/160)→η₀=δcut*(ρ₀/8)*ξroot/1000→0<ηbal→ηbal≤η₀→
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃mBalance mCover:ℕ,1≤mBalance ∧ 1≤mCover ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δ rate d buffer β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel K buffer ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover:=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,
    hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,hchoose⟩:=
    ordinary_actual_trace_fine_profile_rate_shared_numeric_local_host mWheel K buffer hm hbuffer
      ρ₀ hmin href δlimit a ρ θ α pmin ηProfile d hρ₀ hhmin hhref hδlimit ha hρ hθ hα hpmin hηProfile
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,
    hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,?_⟩
  intro ε hε hεvortex rateParent hrateParent
  obtain ⟨ζ,δ,rate,hζ,hζlimit',hζrate,hδ,hδα,hrate,hchoose⟩:=hchoose ε hε hεvortex rateParent hrateParent
  refine ⟨ζ,δ,rate,hζ,hζlimit',hζrate,hδ,hδα,hrate,?_⟩
  intro aLoad ξroot η₀ ηbal haLoad haLoad1 hξroot hη₀ hηbal hηbal0 β hβ hβ1 hβδ C hC
  obtain ⟨ξ,η₀',hξeq,hηeq,hξ,hη₀',hchoose⟩:=hchoose aLoad haLoad haLoad1
  have hξsame:ξ=ξroot:=hξeq.trans hξroot.symm
  have hηsame:η₀'=η₀:=by rw [hηeq,hη₀,hξeq,hξroot]
  have hh:=hchoose ηbal hηbal (by rw [hηsame];exact hηbal0) β hβ hβ1 hβδ C hC
  rw [hξsame] at hh
  exact hh
end Oberwolfach
