module

public import Oberwolfach.OrdinarySpokeExcludedVertexFamily
public import Oberwolfach.FiniteWeightedUniformImpossible

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

theorem ordinary_spoke_excluded_vertex_union (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (T:Finset V) (W:Finset U) (v:V) (u:U) (hv:v∉T) (huW:u∉W):
    (∑ C,if (ordinaryWheelHub C=u ∧ v∈(ordinaryWheelRim C).support) ∧
      (ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) then w C else 0)≤
      (T.card:ℝ)*((r:ℝ)^4*B/Fintype.card V):=by
  have hbound:=ordinary_spoke_excluded_vertex_family Q F H r hr hn hu w B hB hw T v u hv
  have hh:=finite_weighted_uniform_union_excluding_value W T
    (fun C:OrdinaryWheel Q F H r=>ordinaryWheelHub C=u ∧ v∈(ordinaryWheelRim C).support)
    ordinaryWheelHub (fun C z=>z∈(ordinaryWheelRim C).support) w ((r:ℝ)^4*B/Fintype.card V)
    (fun C=>(hw C).1) (by
      intro C hc
      rw [hc.1]
      exact huW) (by
      intro z hz
      convert hbound z hz using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
