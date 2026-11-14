module

public import Oberwolfach.OrdinaryTriangleDeepTraceFineCoverAtLocalBalance
public import Oberwolfach.OrdinaryVortexTraceBufferedTriangleSeparateLoadFineNumericLocalBalanceExplicit
public import Oberwolfach.OrdinaryNonrootNumericSmallerDeep
public import Oberwolfach.OrdinaryFixedVortexNonrootNumericInputsLateLoad

@[expose] public section
/-! The nonroot cover applies at any vortex parent supporting the balanced
host, including the initial parent and all protected later parents. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fine_cover_selector_local_balance_explicit
    (buffer:ℕ) (hbuffer:2≤buffer) (ρ₀ pmin href δlimit κ:ℝ)
    (hρ₀:0<ρ₀) (hpmin:0<pmin) (hhref:0<href) (hδlimit:0<δlimit)
    (hκ:0<κ) (hκ1:κ≤1):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀aLoad:ℝ,0<aLoad→aLoad≤1→∀β:ℝ,0≤β→β≤1/4→∀d:ℕ,
    ∃ξ η₀:ℝ,ξ=min (ε/200) (aLoad^2/160) ∧ η₀=δcut*(ρ₀/8)*ξ/1000 ∧ 0<ξ ∧ 0<η₀ ∧ ∃v₀:ℕ,1≤v₀ ∧ ∀η:ℝ,0≤η→η≤η₀→
    OrdinaryTriangleDeepTraceFineCoverAtLocalBalance buffer ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad κ β η d v₀ :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,hmain⟩:=
    ordinary_vortex_trace_buffered_triangle_separate_load_fine_numeric_local_balance_explicit buffer hbuffer ρ₀ pmin href δlimit κ
      hρ₀ hpmin hhref hδlimit hκ hκ1
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hδcap,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,?_⟩
  intro ε hε hεvortex aLoad haLoad haLoad1 β hβ hβ1 d
  obtain ⟨ξ,η₀,hξeq,hηeq,hξ,hη₀,v₀,hv₀,hcover⟩:=hmain ε hε hεvortex aLoad haLoad haLoad1 β hβ hβ1 d
  refine ⟨ξ,η₀,hξeq,hηeq,hξ,hη₀,v₀,hv₀,?_⟩
  intro η hη hη0
  exact hcover η hη hη0
end Oberwolfach
