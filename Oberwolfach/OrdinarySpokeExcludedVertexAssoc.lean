module

public import Oberwolfach.OrdinaryNonrootWheelLoss

@[expose] public section
/-! The single-root spoke load bound with a left-associated anchor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_spoke_excluded_vertex_load_assoc (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (v z:V) (u:U) (hvz:v≠z):
    (∑ C,if (ordinaryWheelHub C=u ∧ v∈(ordinaryWheelRim C).support) ∧ z∈(ordinaryWheelRim C).support then w C else 0)≤
      (r:ℝ)^4*B/Fintype.card V:=by
  simpa only [and_assoc] using ordinary_spoke_excluded_vertex_load Q F H r hr hn hu w B hB hw v z u hvz
end Oberwolfach
