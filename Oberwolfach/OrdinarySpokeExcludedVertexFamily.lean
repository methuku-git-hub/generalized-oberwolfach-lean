module

public import Oberwolfach.OrdinarySpokeExcludedVertexAssoc

@[expose] public section
/-! The single-excluded-vertex load bound holds simultaneously for every
excluded vertex distinct from the retained endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_spoke_excluded_vertex_family (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (T:Finset V) (v:V) (u:U) (hv:v∉T):
    ∀z∈T,(∑ C,if (ordinaryWheelHub C=u ∧ v∈(ordinaryWheelRim C).support) ∧
      z∈(ordinaryWheelRim C).support then w C else 0)≤(r:ℝ)^4*B/Fintype.card V:=by
  intro z hz
  have hvz:v≠z:=by intro he;subst z;exact hv hz
  exact ordinary_spoke_excluded_vertex_load_assoc Q F H r hr hn hu w B hB hw v z u hvz
end Oberwolfach
