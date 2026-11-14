module

public import Oberwolfach.OrdinarySameSampleReservoirSelectedCostWeights

@[expose] public section
/-! Small positive choices for the certificate's parent margins and for
the later weight-event tolerance, in their respective selection order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_weight_parent_margin_choices
    (ρ₀ cBoundary:ℝ) (hρ₀:0<ρ₀) (hc:0<cBoundary):
    ∃γ eParent hParent κ:ℝ,0<γ ∧ 0<eParent ∧ 0<hParent ∧
      γ ≤ eParent ∧ eParent ≤ cBoundary ∧ hParent ≤ cBoundary ∧
      0<κ ∧ κ ≤ 1 ∧ κ ≤ ρ₀/8 :=by
  refine ⟨cBoundary/4,cBoundary/2,cBoundary/2,min (ρ₀/16) (1/2),by positivity,by positivity,by positivity,
    by linarith,by linarith,by linarith,by positivity,?_,?_⟩
  · exact (min_le_right _ _).trans (by norm_num)
  · have hh:=min_le_left (ρ₀/16) (1/2:ℝ);linarith

theorem ordinary_weight_event_tolerance_choices
    (ηHub α:ℝ) (hη:0<ηHub) (hα:0<α):
    ∃ξ βcap:ℝ,0<ξ ∧ 0<βcap ∧ βcap ≤ 1/4 ∧ βcap ≤ α/8 ∧
      ∀β:ℝ,0 ≤ β  →  β ≤ βcap  →  ξ+2*β<ηHub :=by
  let ξ:ℝ:=ηHub/4
  let βcap:ℝ:=min (ηHub/16) (min (α/16) (1/8))
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hβcap:0<βcap:=by dsimp [βcap];positivity
  have hηcap:βcap ≤ ηHub/16:=min_le_left _ _
  have hαcap:βcap ≤ α/16:=(min_le_right _ _).trans (min_le_left _ _)
  have hquarter:βcap ≤ 1/8:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ξ,βcap,hξ,hβcap,by linarith,by linarith,?_⟩
  intro β hβ hβcap'
  dsimp [ξ]
  linarith
end Oberwolfach
