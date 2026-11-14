module

public import Oberwolfach.OrdinarySpokeExcludedVertexUnion

@[expose] public section
/-! Union the checked single-excluded-vertex bounds at a retained spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_spoke_nonroot_wheel_load_loss (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (T:Finset V) (W:Finset U) (v:V) (u:U) (hv:v∉T) (huW:u∉W):
    (∑ C,if (ordinaryWheelHub C=u ∧ v∈(ordinaryWheelRim C).support) ∧
      (ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) then w C else 0)≤
      (T.card:ℝ)*((r:ℝ)^4*B/Fintype.card V):=by
  exact ordinary_spoke_excluded_vertex_union Q F H r hr hn hu w B hB hw T W v u hv huW
end Oberwolfach
