module

public import Oberwolfach.OrdinaryTriangleInnerNumericCapRefinement

@[expose] public section
/-! The same positive row tolerance can satisfy the initial edit, later
balance, sample, endpoint and sharp-geometry margins simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_common_row_tolerance_choice
    (δInitial δDeep δedit εsample γgeom δend εrows extra:ℝ)
    (hInitial:0<δInitial) (hDeep:0<δDeep) (hEdit:0<δedit) (hSample:0<εsample)
    (hγ:0<γgeom) (hEnd:0<δend) (hRows:0<εrows) (hExtra:0<extra):
    ∃r:ℝ,0<r ∧ r≤δInitial ∧ r≤δDeep ∧ r≤δedit ∧ r≤εsample ∧
      r≤γgeom/1000 ∧ r≤δend/4 ∧ 2*r≤εrows ∧ r≤extra :=by
  let cap:ℝ:=min δInitial (min δDeep (min δedit (min εsample (min (γgeom/1000) (min (δend/4) (min (εrows/2) extra))))))
  have hcap:0<cap:=by dsimp [cap];positivity
  let r:ℝ:=cap/2
  have hr:0<r:=by dsimp [r];positivity
  have hrCap:r≤cap:=by dsimp [r];linarith
  have hI:cap≤δInitial:=min_le_left _ _
  have hD:cap≤δDeep:=(min_le_right _ _).trans (min_le_left _ _)
  have hE:cap≤δedit:=((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hS:cap≤εsample:=(((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hG:cap≤γgeom/1000:=((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hEnd:cap≤δend/4:=(((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hRows':cap≤εrows/2:=((((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hExtra':cap≤extra:=((((((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hRows'':2*r≤εrows:=by linarith
  exact ⟨r,hr,hrCap.trans hI,hrCap.trans hD,hrCap.trans hE,hrCap.trans hS,hrCap.trans hG,hrCap.trans hEnd,hRows'',hrCap.trans hExtra'⟩
end Oberwolfach
