module

public import Oberwolfach.MarkedInnerSpokeColumnFromCorrection
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
/-! The selected correction's own local loss and no-new-spoke bounds imply
all inner-column change bounds at the first vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_inner_spoke_column_vortex_budget
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hm:0<m) (H H':Bool→V→U→Prop) (cap ζ P L:ℝ)
    (hcap:0≤cap) (hζ:ζ≤cap/128)
    (hP:P≤cap*(ε*Fintype.card V)/128) (hL:2*L≤cap*(ε*Fintype.card V)/128)
    (hmark:∀v u,H true v u↔H' true v u)
    (hnoNew:∀u v,v∈Q.extendedVertices 1→H' false v u→H false v u)
    (hloss:∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
      ζ*(Q.extendedVertices 1).card+P+2*L):
    ∀b u,(∑v∈Q.extendedVertices 1,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤
      cap*(Q.extendedVertices 1).card :=by
  let A:=Q.extendedVertices 1
  have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hA:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hζA:=mul_le_mul_of_nonneg_right hζ hA
  have hsizeCap:=mul_le_mul_of_nonneg_left hsize hcap
  have htotal:ζ*(A.card:ℝ)+P+2*L≤cap*(A.card:ℝ):=by
    dsimp only [A] at *
    nlinarith [mul_nonneg hcap hA]
  have hδ:0≤cap*(A.card:ℝ):=mul_nonneg hcap hA
  apply marked_inner_spoke_column_from_correction A H H' (cap*(A.card:ℝ)) hδ hmark hnoNew
  intro u
  exact (hloss u).trans htotal
end Oberwolfach
