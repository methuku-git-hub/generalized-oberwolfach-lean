module

public import Oberwolfach.OrdinaryCertificateFitsDeepInputs

@[expose] public section
/-! Choose row tolerances only after the local certificate's limits are
known, while satisfying every limit needed by the later trace. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_certificate_row_margins
    (δcap δInitial εsample δDeep δend:ℝ)
    (hcap:0<δcap) (hInitial:0<δInitial) (hsample:0<εsample)
    (hDeep:0<δDeep) (hend:0<δend):
    ∃εR εH:ℝ,0<εR ∧ 0<εH ∧
      εR ≤ δcap ∧ εH ≤ δcap ∧ εR ≤ δInitial ∧ εH ≤ δInitial ∧
      εR ≤ εsample ∧ εH ≤ εsample ∧ εR ≤ δDeep ∧ εH ≤ δDeep ∧
      εR ≤ δend/4 ∧ εH ≤ δend/4 :=by
  let row:=min δcap (min δInitial (min εsample (min δDeep (δend/4))))
  have hrow:0<row:=by dsimp [row]; positivity
  have h₁:row ≤ δcap:=min_le_left _ _
  have h₂:row ≤ δInitial:=le_trans (min_le_right _ _) (min_le_left _ _)
  have h₃:row ≤ εsample:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h₄:row ≤ δDeep:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h₅:row ≤ δend/4:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  exact ⟨row,row,hrow,hrow,h₁,h₁,h₂,h₂,h₃,h₃,h₄,h₄,h₅,h₅⟩
end Oberwolfach
