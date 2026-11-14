module

public import Oberwolfach.MarkedInnerSpokeColumnVortexBudget
public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The actual retained-spoke loss estimate meets the level-zero inner budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_physical_spoke_loss_budget
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hm:0<m) (H H':Bool→V→U→Prop) (cap ζ P L:ℝ)
    (hcap:0≤cap) (hζ:ζ≤cap/128)
    (hP:P≤cap*(ε*Fintype.card V)/128) (hL:2*L≤cap*(ε*Fintype.card V)/128)
    (hloss:∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
      ζ*(Q.extendedVertices 1).card+P+2*L):
    ∀u,(((Q.extendedVertices 1).filter (fun v=>H false v u ∧ ¬H' false v u)).card:ℝ)≤
      cap*((markedVortexInnerVertices Q 0).card:ℝ):=by
  let A:=Q.extendedVertices 1
  have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hA:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hζA:=mul_le_mul_of_nonneg_right hζ hA
  have hsizeCap:=mul_le_mul_of_nonneg_left hsize hcap
  have htotal:ζ*(A.card:ℝ)+P+2*L≤cap*(A.card:ℝ):=by
    dsimp only [A] at *
    nlinarith [mul_nonneg hcap hA]
  intro u
  have hc:((markedVortexInnerVertices Q 0).card:ℝ)=(A.card:ℝ):=by
    exact_mod_cast (marked_vortex_inner_cardinalities Q 0).1
  rw [hc]
  exact (hloss u).trans htotal
end Oberwolfach
