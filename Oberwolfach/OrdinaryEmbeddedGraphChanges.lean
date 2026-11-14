module

public import Oberwolfach.OrdinaryGraphChangesDegree
public import Oberwolfach.OrdinaryMappedDifferenceDegree

@[expose] public section
/-! A symmetric rim edit gives bounded degrees on both sides after embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem ordinary_embedded_graph_difference_bounds (φ:V↪W) (R Q:SimpleGraph V) (L:ℝ)
    (hL:0≤L) (h:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L):
    (∀z,(((R.map φ)\(Q.map φ)).degree z:ℝ)≤L) ∧
    (∀z,(((Q.map φ)\(R.map φ)).degree z:ℝ)≤L):=by
  obtain ⟨hRQ,hQR⟩:=ordinary_graph_changes_degree R Q L h
  constructor
  · intro z
    have hh:=ordinary_mapped_difference_degree_bound R Q φ L hL
      (by intro v;convert hRQ v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) z
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro z
    have hh:=ordinary_mapped_difference_degree_bound Q R φ L hL
      (by intro v;convert hQR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) z
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
