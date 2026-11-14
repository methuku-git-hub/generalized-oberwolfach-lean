module

public import Oberwolfach.OrdinaryInducedParentRegularity

@[expose] public section
/-! The actual parent balance and its density margin force the inner
    degree centre into the range needed for cycle weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_parent_center_bounds_from_balance
    (P:SimpleGraph V) (A:Finset V) (Z:Finset U) (pR pH density e δ:ℝ)
    (hA:A.Nonempty) (hpR:0≤pR) (hδ:δ≤1) (hdensity:(1/2:ℝ)+δ≤density)
    (hmin:∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hparent:∀v,|pR*(P.neighborFinset v∩A).card-2*pH*Z.card|≤e)
    (herr:e≤δ*pR*A.card):
    pR*(A.card:ℝ)/2≤2*pH*Z.card ∧ 2*pH*Z.card≤2*pR*A.card:=by
  obtain ⟨v,hv⟩:=hA
  have hA0:(0:ℝ)≤A.card:=by positivity
  have hmin':density*A.card≤((P.neighborFinset v∩A).card:ℝ):=by simpa only [Finset.inter_comm] using hmin v
  have hmax:((P.neighborFinset v∩A).card:ℝ)≤A.card:=by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hminp:=mul_le_mul_of_nonneg_left hmin' hpR
  have hmaxp:=mul_le_mul_of_nonneg_left hmax hpR
  have hden:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdensity hpR) hA0
  have hδp:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ hpR) hA0
  have habs:=abs_le.mp (hparent v)
  constructor <;> nlinarith only [hminp,hmaxp,hden,hδp,habs.1,habs.2,herr]
end Oberwolfach
