module

public import Oberwolfach.OrdinaryBoundaryIndexCountFromInnerSize

@[expose] public section
/-! Both index families fit the quadratic bound in the vertex inner set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_index_count_from_inner_size_both
    (A:Finset V) (Z:Finset U) (K:ℝ)
    (hK:K≤A.card) (hV:(Fintype.card V:ℝ)≤K*A.card) (hU:(Fintype.card U:ℝ)≤K*A.card):
    Fintype.card {u:U // u∉Z}≤A.card^2 ∧ Fintype.card {v:V // v∉A}≤A.card^2:=by
  have hA:0≤(A.card:ℝ):=by positivity
  have hquad:K*(A.card:ℝ)≤(A.card:ℝ)^2:=by
    have hh:=mul_le_mul_of_nonneg_right hK hA
    nlinarith only [hh]
  have hJ:Fintype.card {u:U // u∉Z}≤Fintype.card U:=Fintype.card_subtype_le _
  have hI:Fintype.card {v:V // v∉A}≤Fintype.card V:=Fintype.card_subtype_le _
  have hJ':(Fintype.card {u:U // u∉Z}:ℝ)≤(A.card:ℝ)^2:=
    (Nat.cast_le.mpr hJ).trans (hU.trans hquad)
  have hI':(Fintype.card {v:V // v∉A}:ℝ)≤(A.card:ℝ)^2:=
    (Nat.cast_le.mpr hI).trans (hV.trans hquad)
  constructor
  · exact_mod_cast hJ'
  · exact_mod_cast hI'
end Oberwolfach
