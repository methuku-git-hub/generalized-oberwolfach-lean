module

public import Oberwolfach.OrdinaryLocalWeightBounds
public import Oberwolfach.OrdinaryCycleIncidence

@[expose] public section
/-! The fixed normalized triangle coefficients satisfy the nonnegativity and
inverse-square bound required by the raw potential concentration theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ordinary_triangle_potential_coefficient_bounds
    (P : SimpleGraph V) (p pR pH D cLo cHi : ℝ) (hn : 0<Fintype.card V)
    (hp : 0<p) (hp1:p≤1) (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hcLo:0<cLo) (hcHi:0≤cHi)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (weight:OrdinaryCycle P 3→ℝ)
    (hweight:∀C,cLo/(Fintype.card V:ℝ)≤weight C ∧ weight C≤cHi/(Fintype.card V:ℝ)) :
    ∀ C, 0≤2*weight C/(D*pR^3*pH^2) ∧
      2*weight C/(D*pR^3*pH^2)≤(4*cHi/p^7)/(Fintype.card V:ℝ)^(3-1) := by
  intro C
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  have hh := ordinary_local_coefficient_bounds 2 1 (by omega) (Fintype.card V) D p pR pH cLo cHi (weight C)
    hnR hp hp1 hpR hpR1 hpH hpH1 (by omega) hDlo hDhi hcLo hcHi (by simpa using hweight C)
  norm_num only at hh ⊢
  constructor
  · exact (div_nonneg hcLo.le (by positivity)).trans hh.1
  · exact hh.2
end Oberwolfach
