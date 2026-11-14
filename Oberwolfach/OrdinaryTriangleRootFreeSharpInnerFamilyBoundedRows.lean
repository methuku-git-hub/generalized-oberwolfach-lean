module

public import Oberwolfach.OrdinaryTriangleRootFreeSharpInnerFamilyBeforeSpacing
public import Oberwolfach.OrdinaryTriangleRootFreeSharpInnerBoundedRowsBeforeConflict

@[expose] public section
/-! The root-free family retains a row tolerance below the geometric cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_sharp_inner_family_bounded_rows (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δref:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δref→δref<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀κe pmin bHub BHub:ℝ,0<κe→0<pmin→pmin≤1→0<bHub→0≤BHub→
    ∃εf ηhub ηend ζfresh εrows:ℝ,0<εf ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζfresh ∧ 0<εrows ∧
      εrows≤min (pmin^4/16) (pmin^3/2) ∧
      OrdinaryTriangleRootFreeSharpInnerAfterChoice α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows :=by
  obtain ⟨N,hcert⟩:=ordinary_triangle_root_free_sharp_inner_bounded_rows_before_conflict α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δref hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hlinear,hcert⟩:=hcert k hk ω β b B hpack δref hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hlinear,?_⟩
  intro κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
  exact hcert κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
end Oberwolfach
