module

public import Oberwolfach.OrdinaryTriangleInnerSelectedNumericDomain

@[expose] public section
/-! A later positive spacing cap may shrink the already selected inner
numerical cap without changing any of its earlier witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_numeric_cap_refinement
    (α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap:ℝ)
    (ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap:ℝ)
    (hselected:OrdinaryTriangleInnerSelectedNumericDomain α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap
      ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap)
    (cap:ℝ) (hcap:0<cap):
    ∃βcap':ℝ,0<βcap' ∧ βcap'≤βcap ∧ βcap'≤cap ∧
      OrdinaryTriangleInnerSelectedNumericDomain α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap
        ξ Kdom Bweight tHub eEvent hEvent capHub γold κold δ tpot lamInner bold Bold βcap' :=by
  obtain ⟨hξ,hξη,hK,hB,ht,he,hh,hHub,heP,hhP,hKdom,hsetup,hdeep,hinner,hβcap,hother,hspacing⟩:=hselected
  let βcap':ℝ:=min βcap cap/2
  have hβcap':0<βcap':=by dsimp [βcap'];positivity
  have hsmall:βcap'≤βcap:=by dsimp [βcap'];have h:=min_le_left βcap cap;linarith
  have hsmallCap:βcap'≤cap:=by dsimp [βcap'];have h:=min_le_right βcap cap;linarith
  refine ⟨βcap',hβcap',hsmall,hsmallCap,hξ,hξη,hK,hB,ht,he,hh,hHub,heP,hhP,hKdom,hsetup,hdeep,hinner,
    hβcap',hsmall.trans hother,?_⟩
  intro β hβ hβ'
  exact hspacing β hβ (hβ'.trans hsmall)
end Oberwolfach
