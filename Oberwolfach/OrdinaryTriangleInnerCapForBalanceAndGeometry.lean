module

public import Oberwolfach.OrdinaryTriangleInnerNumericCapRefinement

@[expose] public section
/-! A single refined spacing cap meets the initial edit, both protected
balances and the later sharp-geometry bound without replacing earlier data. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_cap_for_balance_and_geometry
    (α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap:ℝ)
    (ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap:ℝ)
    (hselected:OrdinaryTriangleInnerSelectedNumericDomain α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap
      ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap)
    (δInitial δDeep δedit γgeom:ℝ) (hInitial:0<δInitial) (hDeep:0<δDeep) (hEdit:0<δedit) (hγ:0<γgeom):
    ∃βcap':ℝ,0<βcap' ∧ βcap'≤βcap ∧ βcap'≤δInitial ∧ βcap'≤δDeep ∧ βcap'≤δedit ∧ βcap'≤γgeom/1000 ∧
      OrdinaryTriangleInnerSelectedNumericDomain α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap
        ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap' :=by
  let cap:ℝ:=min δInitial (min δDeep (min δedit (γgeom/1000)))
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨βcap',hβ,hβold,hβcap,hselected'⟩:=ordinary_triangle_inner_numeric_cap_refinement
    α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap
    ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap hselected cap hcap
  have hI:cap≤δInitial:=min_le_left _ _
  have hD:cap≤δDeep:=(min_le_right _ _).trans (min_le_left _ _)
  have hE:cap≤δedit:=((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hG:cap≤γgeom/1000:=((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  exact ⟨βcap',hβ,hβold,hβcap.trans hI,hβcap.trans hD,hβcap.trans hE,hβcap.trans hG,hselected'⟩
end Oberwolfach
