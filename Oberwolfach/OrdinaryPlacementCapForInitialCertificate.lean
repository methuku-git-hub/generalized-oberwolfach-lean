module

public import Oberwolfach.OrdinaryPlacementStage

@[expose] public section
/-! The later placement cap can satisfy both the original edit limit and
the already selected first-level certificate tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_cap_for_initial_certificate
    (capEdit ηedit:ℝ) (hcap:0<capEdit) (hη:0<ηedit):
    ∃capChosen:ℝ,0<capChosen ∧ capChosen≤capEdit ∧ capChosen≤ηedit ∧
      ∀(m dNeed:ℕ) (α lamList ζList δ θ κ b z matchErr σ κ':ℝ),
        OrdinaryPlacementStage m dNeed α lamList ζList capChosen δ θ κ b z matchErr σ κ'→
        5*Real.sqrt δ≤ηedit ∧ σ≤ηedit :=by
  let capChosen:=min capEdit ηedit
  have hChosen:0<capChosen:=by dsimp [capChosen]; positivity
  have hEdit:capChosen≤capEdit:=min_le_left _ _
  have hEta:capChosen≤ηedit:=min_le_right _ _
  refine ⟨capChosen,hChosen,hEdit,hEta,?_⟩
  intro m dNeed α lamList ζList δ θ κ b z matchErr σ κ' hstage
  obtain ⟨_,_,_,hsqrt,_,_,_,_,_,_,_,_,hσ,_⟩:=hstage
  exact ⟨hsqrt.trans hEta,hσ.trans hEta⟩
end Oberwolfach
