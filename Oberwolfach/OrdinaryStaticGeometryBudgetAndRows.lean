module

public import Oberwolfach.OrdinaryInitialPlacementBudgetChoice
public import Oberwolfach.OrdinaryTriangleCommonRowToleranceChoice

@[expose] public section
/-! One placement budget and one row tolerance meet the initial, later,
sharp-geometry and endpoint bounds of the selected wheel certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_static_geometry_budget_and_rows
    (ηedit ζ ε capOriginal δInitial δDeep δedit εsample γgeom δend δcap εrows:ℝ)
    (hη:0<ηedit) (hζ:0<ζ) (hε:0<ε) (hcap:0<capOriginal)
    (hInitial:0<δInitial) (hDeep:0<δDeep) (hEdit:0<δedit) (hSample:0<εsample)
    (hγ:0<γgeom) (hEnd:0<δend) (hCap:0<δcap) (hRows:0<εrows):
    ∃ηBudget capEdit row:ℝ,
      0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζ*ε/2 ∧
      0<capEdit ∧ capEdit≤capOriginal ∧ capEdit≤ηBudget ∧
      0<row ∧ row≤δInitial ∧ row≤δDeep ∧ row≤δedit ∧ row≤εsample ∧
      row≤γgeom/1000 ∧ row≤δend/4 ∧ 2*row≤εrows ∧ row≤δcap :=by
  obtain ⟨ηBudget,capEdit,hBudget,hBudgetη,hsmall,hEditCap,hOriginal,hEditBudget⟩:=
    ordinary_initial_placement_budget_choice ηedit ζ ε capOriginal hη hζ hε hcap
  obtain ⟨row,hrow,hI,hD,hE,hS,hG,hEnd',hRows',hExtra⟩:=
    ordinary_triangle_common_row_tolerance_choice δInitial δDeep δedit εsample γgeom δend εrows δcap
      hInitial hDeep hEdit hSample hγ hEnd hRows hCap
  exact ⟨ηBudget,capEdit,row,hBudget,hBudgetη,hsmall,hEditCap,hOriginal,hEditBudget,
    hrow,hI,hD,hE,hS,hG,hEnd',hRows',hExtra⟩
end Oberwolfach
